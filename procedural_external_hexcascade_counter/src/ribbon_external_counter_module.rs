//! # Ribbon: "It's tape all the way down."
//!
//! Procedural External Hex Cascade Counter - Zero-Heap Version
//!
//! Externalized procedural variables for arbitrary-precision counting.
//! Never loads the entire value into a single integer variable.
//! Processes digit-by-digit incrementally.
//! **All operations use stack-only memory.**
//!
//! ## Purpose
//! Count things of unknown magnitude without overflow:
//! - Files in directories
//! - Time units (Y2K/2038-proof timestamps)
//! - Events in long-running systems
//! - Any scenario where the count size is unknown upfront
//!
//! ## Architecture
//! Pre-allocated stack buffers with automatic tier promotion:
//! - Tier 0: 4 bytes  (0 to 65,535 decimal)
//! - Tier 1: 8 bytes  (0 to 4,294,967,295 decimal)
//! - Tier 2: 16 bytes (0 to ~18 quintillion decimal)
//! - Tier 3: 256 bytes (astronomical)
//! - Tier 4: 2048 bytes (theoretical maximum)
//!
//! Starts tiny (4 bytes), grows automatically only when needed.
//!
//! ## Storage Format
//! - Internal: Hex ASCII ('0'-'9', 'A'-'F') for efficiency
//! - Output: Human-readable decimal string (written to caller-provided buffer)
//!
//! ## Policy
//! - **No heap allocation** (all buffers stack-only)
//! - No dynamic allocation (all buffers pre-allocated on stack)
//! - No overflow (automatic promotion to larger tiers)
//! - No unwrap (all errors handled explicitly)
//! - No unsafe code
//! - Bounded loops with explicit capacity limits

use std::io::{Error, ErrorKind, Result};

// ============================================================================
// BUFFER TIER CAPACITIES
// ============================================================================

/// Tier 0: Tiny buffer capacity in bytes (4 hex digits = up to 65,535 decimal)
const TIER_0_CAPACITY: usize = 4;

/// Tier 1: Small buffer capacity in bytes (8 hex digits = up to ~4 billion decimal)
const TIER_1_CAPACITY: usize = 8;

/// Tier 2: Medium buffer capacity in bytes (16 hex digits = up to u64::MAX+)
const TIER_2_CAPACITY: usize = 16;

/// Tier 3: Large buffer capacity in bytes (256 hex digits)
const TIER_3_CAPACITY: usize = 256;

/// Tier 4: Maximum buffer capacity in bytes (2048 hex digits)
const TIER_4_CAPACITY: usize = 2048;

/// Maximum number of iterations for any single loop operation
/// Prevents infinite loops from data corruption or cosmic ray bit flips
const MAX_LOOP_ITERATIONS: usize = TIER_4_CAPACITY;

/// Maximum decimal digits needed to represent largest hex value
/// TIER_4_CAPACITY hex digits = 2048 * 4 bits = 8192 bits
/// log10(2^8192) ≈ 2466 decimal digits (round up to 2500 for safety)
const MAX_DECIMAL_DIGITS: usize = 2500;

// ============================================================================
// ACTIVE TIER ENUMERATION
// ============================================================================

/// Identifies which pre-allocated buffer tier is currently active
///
/// Counter automatically promotes to next tier when current capacity is exceeded.
/// Promotion is a rare exception-handling event (e.g., going from 65,535 to 65,536).
///
/// # Invariants
/// - Counter always starts at Tier0
/// - Promotion is one-way (never demotes)
/// - Maximum tier is Tier4 (no further promotion possible)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ActiveTier {
    /// Tier 0: 4 bytes (most common case, handles typical file counts)
    Tier0,
    /// Tier 1: 8 bytes (handles large directories, exceeds u32::MAX)
    Tier1,
    /// Tier 2: 16 bytes (handles extreme cases, exceeds u64::MAX)
    Tier2,
    /// Tier 3: 256 bytes (astronomical counts)
    Tier3,
    /// Tier 4: 2048 bytes (theoretical maximum for this system)
    Tier4,
}

impl ActiveTier {
    /// Get capacity in bytes for this tier
    ///
    /// # Returns
    /// Number of hex digit ASCII characters this tier can store
    fn capacity(&self) -> usize {
        match self {
            ActiveTier::Tier0 => TIER_0_CAPACITY,
            ActiveTier::Tier1 => TIER_1_CAPACITY,
            ActiveTier::Tier2 => TIER_2_CAPACITY,
            ActiveTier::Tier3 => TIER_3_CAPACITY,
            ActiveTier::Tier4 => TIER_4_CAPACITY,
        }
    }

    /// Get next higher tier if available
    ///
    /// # Returns
    /// - `Some(next_tier)` if promotion is possible
    /// - `None` if already at maximum tier
    fn next_tier(&self) -> Option<ActiveTier> {
        match self {
            ActiveTier::Tier0 => Some(ActiveTier::Tier1),
            ActiveTier::Tier1 => Some(ActiveTier::Tier2),
            ActiveTier::Tier2 => Some(ActiveTier::Tier3),
            ActiveTier::Tier3 => Some(ActiveTier::Tier4),
            ActiveTier::Tier4 => None,
        }
    }

    /// Get tier number for logging and diagnostics
    fn tier_number(&self) -> u8 {
        match self {
            ActiveTier::Tier0 => 0,
            ActiveTier::Tier1 => 1,
            ActiveTier::Tier2 => 2,
            ActiveTier::Tier3 => 3,
            ActiveTier::Tier4 => 4,
        }
    }
}

// ============================================================================
// MAIN COUNTER STRUCTURE
// ============================================================================

/// Cascading hex counter with automatic tier promotion
///
/// # Design
/// All five buffer tiers are pre-allocated on the stack (2332 bytes total).
/// Counter starts using the smallest buffer (Tier 0: 4 bytes).
/// Automatically promotes to larger buffers only when capacity is exceeded.
///
/// # Memory Behavior
/// **Zero heap allocations.** All operations use stack-only memory.
/// OS lazy-commits memory pages. Unused tiers don't consume physical RAM
/// until first write (during promotion).
///
/// # Storage Strategy
/// - Internal storage: Hex digits as ASCII bytes ('0'-'9', 'A'-'F')
/// - External output: Human-readable decimal strings written to caller buffers
/// - Hex is 20-30% more memory-efficient than decimal
///
/// # Thread Safety
/// Not thread-safe. If concurrent access needed, wrap in Mutex.
///
/// # Example
/// ```
/// let mut counter = CascadingHexCounter::new();
/// let mut decimal_buffer = [0u8; 100];
///
/// for item in items {
///     counter.increment()?;
/// }
///
/// let len = counter.to_decimal(&mut decimal_buffer)?;
/// let decimal_str = std::str::from_utf8(&decimal_buffer[..len])?;
/// println!("Total count: {}", decimal_str);
/// ```
pub struct CascadingHexCounter {
    /// Tier 0 buffer: 4 bytes (handles 99% of real-world cases)
    buffer_tier_0: [u8; TIER_0_CAPACITY],

    /// Tier 1 buffer: 8 bytes (handles large counts)
    buffer_tier_1: [u8; TIER_1_CAPACITY],

    /// Tier 2 buffer: 16 bytes (handles extreme counts)
    buffer_tier_2: [u8; TIER_2_CAPACITY],

    /// Tier 3 buffer: 256 bytes (handles astronomical counts)
    buffer_tier_3: [u8; TIER_3_CAPACITY],

    /// Tier 4 buffer: 2048 bytes (theoretical maximum)
    buffer_tier_4: [u8; TIER_4_CAPACITY],

    /// Currently active buffer tier
    current_tier: ActiveTier,

    /// Number of valid hex digits in active buffer (counted from right)
    ///
    /// # Invariant
    /// Must satisfy: 1 <= digit_count <= current_tier.capacity()
    digit_count: usize,
}

// ============================================================================
// CORE IMPLEMENTATION
// ============================================================================

impl CascadingHexCounter {
    /// Create new counter initialized to zero
    ///
    /// # Initial State
    /// - Active tier: Tier 0 (4 bytes)
    /// - Value: "0" (single hex digit)
    /// - Memory touched: ~4-8 bytes (OS page granularity)
    ///
    /// # Example
    /// ```
    /// let counter = CascadingHexCounter::new();
    /// let mut buf = [0u8; 10];
    /// let len = counter.to_decimal(&mut buf).unwrap();
    /// assert_eq!(&buf[..len], b"0");
    /// ```
    pub fn new() -> Self {
        // Initialize Tier 0 with '0' at rightmost position
        let mut buffer_0 = [0u8; TIER_0_CAPACITY];
        buffer_0[TIER_0_CAPACITY - 1] = b'0';

        // Defensive: Ensure initial state is valid
        assert!(TIER_0_CAPACITY > 0, "Tier 0 capacity must be positive");

        CascadingHexCounter {
            buffer_tier_0: buffer_0,
            buffer_tier_1: [0u8; TIER_1_CAPACITY],
            buffer_tier_2: [0u8; TIER_2_CAPACITY],
            buffer_tier_3: [0u8; TIER_3_CAPACITY],
            buffer_tier_4: [0u8; TIER_4_CAPACITY],
            current_tier: ActiveTier::Tier0,
            digit_count: 1,
        }
    }

    /// Get immutable reference to currently active buffer
    ///
    /// # Returns
    /// Slice containing all bytes of active tier's buffer
    ///
    /// # Note
    /// Only rightmost `digit_count` bytes contain valid hex digits.
    fn get_active_buffer(&self) -> &[u8] {
        match self.current_tier {
            ActiveTier::Tier0 => &self.buffer_tier_0[..],
            ActiveTier::Tier1 => &self.buffer_tier_1[..],
            ActiveTier::Tier2 => &self.buffer_tier_2[..],
            ActiveTier::Tier3 => &self.buffer_tier_3[..],
            ActiveTier::Tier4 => &self.buffer_tier_4[..],
        }
    }

    /// Get mutable reference to currently active buffer
    ///
    /// # Returns
    /// Mutable slice containing all bytes of active tier's buffer
    ///
    /// # Borrowing
    /// Takes exclusive mutable borrow of self. Cannot access other fields
    /// while this borrow is active. Store needed values before calling.
    fn get_active_buffer_mut(&mut self) -> &mut [u8] {
        match self.current_tier {
            ActiveTier::Tier0 => &mut self.buffer_tier_0[..],
            ActiveTier::Tier1 => &mut self.buffer_tier_1[..],
            ActiveTier::Tier2 => &mut self.buffer_tier_2[..],
            ActiveTier::Tier3 => &mut self.buffer_tier_3[..],
            ActiveTier::Tier4 => &mut self.buffer_tier_4[..],
        }
    }

    /// Get slice containing only valid hex digits from active buffer
    ///
    /// # Returns
    /// Slice of rightmost `digit_count` bytes representing current value
    ///
    /// # Example
    /// ```text
    /// Buffer: [0, 0, ..., 'A', 'B', 'C', 'D']
    ///                      ^-----------^
    ///                      Valid digits (digit_count=4)
    /// Represents: 0xABCD
    /// ```
    fn get_valid_digits(&self) -> &[u8] {
        let capacity = self.current_tier.capacity();
        let start = capacity - self.digit_count;
        let buffer = self.get_active_buffer();

        // Defensive: Ensure slice bounds are valid
        assert!(
            start <= capacity,
            "Invalid buffer slice: start exceeds capacity"
        );
        assert!(self.digit_count <= capacity, "Digit count exceeds capacity");

        &buffer[start..capacity]
    }

    /// Promote to next higher tier (rare exception-handling operation)
    ///
    /// # Process
    /// 1. Verify next tier exists (error if at maximum)
    /// 2. Copy valid digits from current buffer to new buffer
    /// 3. Update current_tier to point to new buffer
    ///
    /// # Memory Behavior
    /// First write to new buffer causes OS to commit physical pages.
    /// **No heap allocation.**
    ///
    /// # Errors
    /// Returns `OutOfMemory` if already at Tier 4 (maximum capacity)
    ///
    /// # Edge Cases
    /// - Promotion preserves exact value
    /// - digit_count unchanged
    /// - Old buffer remains intact (for debugging)
    fn promote_to_next_tier(&mut self) -> Result<()> {
        // Attempt to get next tier
        let next_tier = self.current_tier.next_tier().ok_or_else(|| {
            Error::new(
                ErrorKind::OutOfMemory,
                "Counter at maximum capacity: Tier 4 exceeded",
            )
        })?;

        // Calculate buffer positions
        let old_capacity = self.current_tier.capacity();
        let new_capacity = next_tier.capacity();
        let old_start = old_capacity - self.digit_count;
        let new_start = new_capacity - self.digit_count;

        // Defensive: Verify capacities are sane
        assert!(
            new_capacity > old_capacity,
            "New capacity must exceed old capacity"
        );
        assert!(
            self.digit_count <= old_capacity,
            "Digit count exceeds old capacity"
        );

        // Copy valid digits from old buffer to new buffer
        // Must do this carefully to avoid borrow conflicts
        match self.current_tier {
            ActiveTier::Tier0 => {
                let source = &self.buffer_tier_0[old_start..old_capacity];
                self.buffer_tier_1[new_start..new_capacity].copy_from_slice(source);
            }
            ActiveTier::Tier1 => {
                let source = &self.buffer_tier_1[old_start..old_capacity];
                self.buffer_tier_2[new_start..new_capacity].copy_from_slice(source);
            }
            ActiveTier::Tier2 => {
                let source = &self.buffer_tier_2[old_start..old_capacity];
                self.buffer_tier_3[new_start..new_capacity].copy_from_slice(source);
            }
            ActiveTier::Tier3 => {
                let source = &self.buffer_tier_3[old_start..old_capacity];
                self.buffer_tier_4[new_start..new_capacity].copy_from_slice(source);
            }
            ActiveTier::Tier4 => {
                unreachable!("Cannot promote beyond Tier 4");
            }
        }

        // Activate new tier
        self.current_tier = next_tier;

        Ok(())
    }

    /// Convert ASCII hex character to numeric value (0-15)
    ///
    /// # Arguments
    /// * `hex_char` - ASCII byte representing hex digit
    ///
    /// # Returns
    /// - `Some(value)` where value is 0-15 for valid hex
    /// - `None` for invalid characters
    ///
    /// # Examples
    /// - b'0' → Some(0)
    /// - b'9' → Some(9)
    /// - b'A' or b'a' → Some(10)
    /// - b'F' or b'f' → Some(15)
    /// - b'G' → None
    fn hex_char_to_value(hex_char: u8) -> Option<u8> {
        match hex_char {
            b'0'..=b'9' => Some(hex_char - b'0'),
            b'A'..=b'F' => Some(hex_char - b'A' + 10),
            b'a'..=b'f' => Some(hex_char - b'a' + 10),
            _ => None,
        }
    }

    /// Convert numeric value (0-15) to uppercase ASCII hex character
    ///
    /// # Arguments
    /// * `value` - Numeric value from 0 to 15
    ///
    /// # Returns
    /// - `Some(character)` for valid range 0-15
    /// - `None` for values >= 16
    ///
    /// # Examples
    /// - 0 → Some(b'0')
    /// - 9 → Some(b'9')
    /// - 10 → Some(b'A')
    /// - 15 → Some(b'F')
    /// - 16 → None
    fn value_to_hex_char(value: u8) -> Option<u8> {
        match value {
            0..=9 => Some(b'0' + value),
            10..=15 => Some(b'A' + value - 10),
            _ => None,
        }
    }

    /// Increment counter by one (core counting operation)
    ///
    /// # Algorithm
    /// Standard base-16 addition with carry propagation:
    /// 1. Start at rightmost digit (least significant)
    /// 2. Add 1, check if result >= 16 (carry condition)
    /// 3. If carry: digit becomes 0, continue left
    /// 4. If no carry: update digit, done
    /// 5. If carry reaches left edge: extend left or promote tier
    ///
    /// # Edge Cases
    /// - "0" → "1" (simple increment, no carry)
    /// - "F" → "10" (carry, extend one digit left)
    /// - "FF" → "100" (carry propagates, extend left)
    /// - "FFFF" in Tier 0 → promote to Tier 1, then → "10000"
    ///
    /// # Errors
    /// Returns error if:
    /// - Invalid hex digit found (data corruption)
    /// - At Tier 4 maximum capacity (cannot grow further)
    ///
    /// # Performance
    /// - Best case: O(1) - rightmost digit not 'F'
    /// - Worst case: O(n) - all digits 'F', must process all + extend
    /// - Amortized: O(1) - carry is rare
    ///
    /// # Loop Bounds
    /// All loops bounded by MAX_LOOP_ITERATIONS (cosmic ray protection)
    ///
    /// # Memory
    /// **Zero heap allocation.** All operations on stack.
    pub fn increment(&mut self) -> Result<()> {
        // Store values needed before taking mutable borrow
        // (Avoids borrow checker conflicts)
        let capacity = self.current_tier.capacity();
        let count = self.digit_count;
        let start = capacity - count;
        let can_extend = count < capacity;

        // Defensive: Verify state consistency
        assert!(count > 0, "Digit count must be positive");
        assert!(count <= capacity, "Digit count exceeds capacity");
        assert!(
            count <= MAX_LOOP_ITERATIONS,
            "Digit count exceeds safety limit"
        );

        // Get mutable access to buffer (begins exclusive borrow)
        let buffer = self.get_active_buffer_mut();

        // Carry flag: starts as 1 (adding 1 to number)
        let mut carry = 1u8;

        // Process digits right to left (bounded loop)
        for loop_index in 0..count {
            // Defensive: Loop bound check
            assert!(
                loop_index < MAX_LOOP_ITERATIONS,
                "Loop iteration exceeds safety limit"
            );

            // Calculate buffer index (right to left)
            let buffer_index = capacity - 1 - loop_index;

            // Only process if carry remains
            if carry > 0 {
                // Convert ASCII to numeric value
                let digit_value =
                    Self::hex_char_to_value(buffer[buffer_index]).ok_or_else(|| {
                        Error::new(
                            ErrorKind::InvalidData,
                            "Corrupted hex digit (possible cosmic ray bit flip)",
                        )
                    })?;

                // Add carry to digit
                let mut new_value = digit_value + carry;

                // Check for carry to next position
                if new_value >= 16 {
                    new_value = 0;
                    carry = 1;
                } else {
                    carry = 0;
                }

                // Convert back to ASCII hex
                let new_char = Self::value_to_hex_char(new_value)
                    .ok_or_else(|| Error::new(ErrorKind::InvalidData, "Invalid hex conversion"))?;

                buffer[buffer_index] = new_char;
            } else {
                // No more carry, done
                break;
            }
        }

        // Release borrow by letting buffer go out of scope

        // If still carrying, need to add new digit to the left
        if carry > 0 {
            if can_extend {
                // Room in current tier: add digit
                let new_start = start - 1;

                // Re-borrow buffer for writing
                {
                    let buffer = self.get_active_buffer_mut();
                    buffer[new_start] = b'1';
                }

                self.digit_count += 1;
            } else {
                // Current tier full: must promote
                self.promote_to_next_tier()?;

                // After promotion, add the carry digit
                let new_capacity = self.current_tier.capacity();
                let new_start = new_capacity - self.digit_count - 1;

                {
                    let buffer = self.get_active_buffer_mut();
                    buffer[new_start] = b'1';
                }

                self.digit_count += 1;
            }
        }

        // Defensive: Verify post-increment state
        assert!(
            self.digit_count > 0,
            "Post-increment: digit count became zero"
        );
        assert!(
            self.digit_count <= self.current_tier.capacity(),
            "Post-increment: digit count exceeds tier capacity"
        );

        Ok(())
    }

    /// Write current value as hexadecimal string to buffer
    ///
    /// # Arguments
    /// * `buffer` - Mutable byte slice to write hex digits into
    ///
    /// # Returns
    /// - `Ok(length)` - Number of bytes written to buffer
    /// - `Err(_)` - Buffer too small
    ///
    /// # Errors
    /// Returns error if buffer is too small to hold result
    ///
    /// # Memory
    /// **Zero heap allocation.** Writes directly to provided buffer.
    ///
    /// # Example
    /// ```
    /// let mut counter = CascadingHexCounter::new();
    /// counter.increment()?;
    ///
    /// let mut hex_buffer = [0u8; 20];
    /// let len = counter.to_hex(&mut hex_buffer)?;
    ///
    /// assert_eq!(&hex_buffer[..len], b"1");
    /// ```
    #[cfg(test)]
    pub fn to_hex(&self, buffer: &mut [u8]) -> Result<usize> {
        let digits = self.get_valid_digits();

        // Defensive: Ensure digits are valid
        assert!(!digits.is_empty(), "Valid digits slice cannot be empty");

        // Check buffer capacity
        if buffer.len() < digits.len() {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                "Buffer too small for hex output",
            ));
        }

        // Copy digits to buffer
        buffer[..digits.len()].copy_from_slice(digits);

        Ok(digits.len())
    }

    /// Convert current hex value to human-readable decimal string in buffer
    ///
    /// # Arguments
    /// * `buffer` - Mutable byte slice to write decimal digits into
    ///
    /// # Returns
    /// - `Ok(length)` - Number of bytes written to buffer
    /// - `Err(_)` - Buffer too small or conversion error
    ///
    /// # Algorithm
    /// Performs arbitrary-precision hex-to-decimal conversion:
    /// 1. Start with decimal accumulator = 0
    /// 2. For each hex digit (left to right):
    ///    - Multiply accumulator by 16
    ///    - Add current hex digit value
    /// 3. Write result to buffer
    ///
    /// # Example Conversion
    /// ```text
    /// Hex: "2BF" (2, 11, 15 in decimal)
    ///
    /// Step 1: acc = 0
    /// Step 2: acc = 0 * 16 + 2 = 2
    /// Step 3: acc = 2 * 16 + 11 = 43
    /// Step 4: acc = 43 * 16 + 15 = 703
    ///
    /// Result: "703"
    /// ```
    ///
    /// # Errors
    /// Returns error if:
    /// - Invalid hex digit found
    /// - Buffer too small to hold result
    ///
    /// # Performance
    /// O(n²) where n is number of hex digits, due to arbitrary precision
    /// multiplication. Acceptable for counting (infrequent reads).
    ///
    /// # Memory
    /// **Zero heap allocation.** Uses fixed-size stack array for intermediate
    /// calculation, writes result directly to provided buffer.
    ///
    /// # Edge Cases
    /// - "0" → "0"
    /// - "A" → "10"
    /// - "FF" → "255"
    /// - "100" → "256"
    ///
    /// # Example
    /// ```
    /// let mut counter = CascadingHexCounter::new();
    /// for _ in 0..100 {
    ///     counter.increment()?;
    /// }
    ///
    /// let mut dec_buffer = [0u8; 50];
    /// let len = counter.to_decimal(&mut dec_buffer)?;
    /// let dec_str = std::str::from_utf8(&dec_buffer[..len])?;
    ///
    /// assert_eq!(dec_str, "100");
    /// ```
    pub fn to_decimal(&self, buffer: &mut [u8]) -> Result<usize> {
        let hex_digits = self.get_valid_digits();

        // Defensive: Ensure we have digits
        assert!(
            !hex_digits.is_empty(),
            "Cannot convert empty hex digits to decimal"
        );

        // Edge case: single zero
        if hex_digits.len() == 1 && hex_digits[0] == b'0' {
            if buffer.is_empty() {
                return Err(Error::new(
                    ErrorKind::InvalidInput,
                    "Buffer too small for decimal output",
                ));
            }
            buffer[0] = b'0';
            return Ok(1);
        }

        // Decimal accumulator: fixed-size array (stack-only)
        // Each u8 represents a single decimal digit 0-9
        let mut decimal_digits = [0u8; MAX_DECIMAL_DIGITS];
        let mut decimal_count: usize = 1; // Start with one digit (0)

        // Process each hex digit left to right (bounded loop)
        for (loop_index, &hex_char) in hex_digits.iter().enumerate() {
            // Defensive: Loop bound check
            assert!(
                loop_index < MAX_LOOP_ITERATIONS,
                "Hex-to-decimal loop iteration exceeds safety limit"
            );

            // Convert hex char to numeric value
            let hex_value = Self::hex_char_to_value(hex_char)
                .ok_or_else(|| Error::new(ErrorKind::InvalidData, "Invalid hex character"))?;

            // Multiply current decimal accumulator by 16
            decimal_count = Self::multiply_decimal_by_16_fixed(&mut decimal_digits, decimal_count)?;

            // Add hex digit value to accumulator
            decimal_count =
                Self::add_to_decimal_fixed(&mut decimal_digits, decimal_count, hex_value)?;
        }

        // Check buffer capacity
        if buffer.len() < decimal_count {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                "Buffer too small for decimal output",
            ));
        }

        // Convert decimal digits to ASCII and write to buffer
        for i in 0..decimal_count {
            let digit = decimal_digits[i];
            assert!(digit <= 9, "Invalid decimal digit");
            buffer[i] = b'0' + digit;
        }

        Ok(decimal_count)
    }

    /// Multiply arbitrary-precision decimal by 16 (in-place, stack-only)
    ///
    /// # Algorithm
    /// 1. Multiply each decimal digit by 16
    /// 2. Propagate carries left
    /// 3. Extend left if final carry exists
    ///
    /// # Arguments
    /// * `digits` - Fixed-size array of decimal digits (0-9)
    /// * `count` - Number of valid digits in array (counted from left)
    ///
    /// # Returns
    /// New count of valid digits after multiplication
    ///
    /// # Example
    /// ```text
    /// Input:  [2, 5, 0, 0, ...] count=2  (represents 25 decimal)
    /// Step 1: [2*16, 5*16, ...] = [32, 80, ...]
    /// Step 2: Propagate carries:
    ///         digit[1]: 80 = 8*10 + 0, carry 8
    ///         [32+8, 0, ...] = [40, 0, ...]
    ///         digit[0]: 40 = 4*10 + 0, carry 4
    ///         [0, 0, ...] with carry 4
    /// Step 3: Shift right and prepend: [4, 0, 0, ...]
    /// Output: [4, 0, 0, ...] count=3 (represents 400 decimal)
    /// Verify: 25 * 16 = 400 ✓
    /// ```
    ///
    /// # Memory
    /// **Zero heap allocation.** All operations on provided fixed array.
    ///
    /// # Errors
    /// Returns error if result would exceed array capacity
    fn multiply_decimal_by_16_fixed(
        digits: &mut [u8; MAX_DECIMAL_DIGITS],
        count: usize,
    ) -> Result<usize> {
        // Defensive: Ensure count is valid
        assert!(count > 0, "Decimal digit count must be positive");
        assert!(
            count <= MAX_DECIMAL_DIGITS,
            "Decimal digit count exceeds limit"
        );
        assert!(
            count <= MAX_LOOP_ITERATIONS,
            "Decimal digit count exceeds safety limit"
        );

        let mut carry = 0u32;

        // Process digits right to left (bounded loop)
        for loop_index in 0..count {
            // Defensive: Loop bound check
            assert!(
                loop_index < MAX_LOOP_ITERATIONS,
                "Multiply loop iteration exceeds safety limit"
            );

            let idx = count - 1 - loop_index;

            // Defensive: Ensure digit is valid (0-9)
            assert!(digits[idx] <= 9, "Invalid decimal digit");

            // Multiply digit by 16 and add carry
            let product = (digits[idx] as u32) * 16 + carry;

            // Extract new digit and carry
            digits[idx] = (product % 10) as u8;
            carry = product / 10;
        }

        // If carry remains, shift digits right and prepend carry digits
        let mut new_count = count;
        if carry > 0 {
            // Calculate how many digits the carry needs
            let mut carry_temp = carry;
            let mut carry_digits = 0usize;
            while carry_temp > 0 {
                carry_temp /= 10;
                carry_digits += 1;
            }

            // Check if we have room
            if new_count + carry_digits > MAX_DECIMAL_DIGITS {
                return Err(Error::new(
                    ErrorKind::OutOfMemory,
                    "Decimal expansion exceeds maximum capacity",
                ));
            }

            // Shift existing digits right
            for i in (0..new_count).rev() {
                digits[i + carry_digits] = digits[i];
            }

            // Insert carry digits at front
            for i in 0..carry_digits {
                let digit_index = carry_digits - 1 - i;
                digits[digit_index] = (carry % 10) as u8;
                carry /= 10;
            }

            new_count += carry_digits;
        }

        Ok(new_count)
    }

    /// Add small value to arbitrary-precision decimal (in-place, stack-only)
    ///
    /// # Arguments
    /// * `digits` - Fixed-size array of decimal digits (0-9)
    /// * `count` - Number of valid digits in array (counted from left)
    /// * `value` - Value to add (0-15, from hex digit)
    ///
    /// # Returns
    /// New count of valid digits after addition
    ///
    /// # Algorithm
    /// 1. Add value to rightmost digit
    /// 2. Propagate carry left if needed
    /// 3. Extend left if carry reaches front
    ///
    /// # Example
    /// ```text
    /// Input:  [2, 9, 9, 0, ...] count=3, value=5  (represents 299 decimal)
    /// Step 1: [2, 9, 9+5, ...] = [2, 9, 14, ...]
    /// Step 2: digit[2]: 14 = 1*10 + 4, carry 1
    ///         [2, 9+1, 4, ...] = [2, 10, 4, ...]
    ///         digit[1]: 10 = 1*10 + 0, carry 1
    ///         [2+1, 0, 4, ...] = [3, 0, 4, ...]
    /// Output: [3, 0, 4, ...] count=3 (represents 304 decimal)
    /// Verify: 299 + 5 = 304 ✓
    /// ```
    ///
    /// # Memory
    /// **Zero heap allocation.** All operations on provided fixed array.
    ///
    /// # Errors
    /// Returns error if result would exceed array capacity
    fn add_to_decimal_fixed(
        digits: &mut [u8; MAX_DECIMAL_DIGITS],
        count: usize,
        value: u8,
    ) -> Result<usize> {
        // Defensive: Validate inputs
        assert!(count > 0, "Decimal digit count must be positive");
        assert!(value <= 15, "Value to add must be 0-15 (single hex digit)");
        assert!(
            count <= MAX_DECIMAL_DIGITS,
            "Decimal digit count exceeds limit"
        );
        assert!(
            count <= MAX_LOOP_ITERATIONS,
            "Decimal digit count exceeds safety limit"
        );

        let mut carry = value as u32;

        // Process digits right to left (bounded loop)
        for loop_index in 0..count {
            // Defensive: Loop bound check
            assert!(
                loop_index < MAX_LOOP_ITERATIONS,
                "Add loop iteration exceeds safety limit"
            );

            let idx = count - 1 - loop_index;

            // Defensive: Validate digit
            assert!(digits[idx] <= 9, "Invalid decimal digit");

            // Add carry to current digit
            let sum = (digits[idx] as u32) + carry;
            digits[idx] = (sum % 10) as u8;
            carry = sum / 10;

            if carry == 0 {
                return Ok(count);
            }
        }

        // If carry remains, shift right and prepend
        if carry > 0 {
            if count >= MAX_DECIMAL_DIGITS {
                return Err(Error::new(
                    ErrorKind::OutOfMemory,
                    "Decimal expansion exceeds maximum capacity",
                ));
            }

            // Shift digits right
            for i in (0..count).rev() {
                digits[i + 1] = digits[i];
            }

            // Insert carry at front
            digits[0] = carry as u8;

            return Ok(count + 1);
        }

        Ok(count)
    }

    /// Reset counter to zero
    ///
    /// # Effects
    /// - Returns to Tier 0
    /// - Sets value to "0"
    /// - Clears Tier 0 buffer (other tiers untouched)
    ///
    /// # Memory
    /// **Zero heap allocation.**
    ///
    /// # Example
    /// ```
    /// let mut counter = CascadingHexCounter::new();
    /// counter.increment()?;
    /// counter.increment()?;
    /// counter.reset()?;
    ///
    /// let mut buf = [0u8; 10];
    /// let len = counter.to_decimal(&mut buf)?;
    /// assert_eq!(&buf[..len], b"0");
    /// ```
    pub fn reset(&mut self) -> Result<()> {
        self.buffer_tier_0 = [0u8; TIER_0_CAPACITY];
        self.buffer_tier_0[TIER_0_CAPACITY - 1] = b'0';
        self.current_tier = ActiveTier::Tier0;
        self.digit_count = 1;

        // Defensive: Verify reset state
        assert_eq!(self.digit_count, 1, "Post-reset: digit count must be 1");
        assert_eq!(
            self.current_tier,
            ActiveTier::Tier0,
            "Post-reset: must be in Tier 0"
        );

        Ok(())
    }

    /// Get current active tier number (for diagnostics)
    ///
    /// # Returns
    /// Tier number: 0, 1, 2, 3, or 4
    pub fn current_tier(&self) -> u8 {
        self.current_tier.tier_number()
    }

    /// Get current digit count (for diagnostics)
    ///
    /// # Returns
    /// Number of hex digits representing current value
    pub fn digit_count(&self) -> usize {
        self.digit_count
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_creation() {
        let counter = CascadingHexCounter::new();

        let mut hex_buf = [0u8; 10];
        let hex_len = counter.to_hex(&mut hex_buf).unwrap();
        assert_eq!(&hex_buf[..hex_len], b"0");

        let mut dec_buf = [0u8; 10];
        let dec_len = counter.to_decimal(&mut dec_buf).unwrap();
        assert_eq!(&dec_buf[..dec_len], b"0");

        assert_eq!(counter.current_tier(), 0);
        assert_eq!(counter.digit_count(), 1);
    }

    #[test]
    fn test_increment_sequence() {
        let mut counter = CascadingHexCounter::new();

        // Use slice of slices: &[&[u8]]
        let expected_hex: &[&[u8]] = &[
            b"0", b"1", b"2", b"3", b"4", b"5", b"6", b"7", b"8", b"9", b"A", b"B", b"C", b"D",
            b"E", b"F",
        ];
        let expected_dec: &[&[u8]] = &[
            b"0", b"1", b"2", b"3", b"4", b"5", b"6", b"7", b"8", b"9", b"10", b"11", b"12", b"13",
            b"14", b"15",
        ];

        for i in 0..16 {
            let mut hex_buf = [0u8; 10];
            let hex_len = counter.to_hex(&mut hex_buf).unwrap();
            assert_eq!(&hex_buf[..hex_len], expected_hex[i]);

            let mut dec_buf = [0u8; 10];
            let dec_len = counter.to_decimal(&mut dec_buf).unwrap();
            assert_eq!(&dec_buf[..dec_len], expected_dec[i]);

            counter.increment().unwrap();
        }
    }

    #[test]
    fn test_carry_to_two_digits() {
        let mut counter = CascadingHexCounter::new();

        for _ in 0..16 {
            counter.increment().unwrap();
        }

        let mut hex_buf = [0u8; 10];
        let hex_len = counter.to_hex(&mut hex_buf).unwrap();
        assert_eq!(&hex_buf[..hex_len], b"10");

        let mut dec_buf = [0u8; 10];
        let dec_len = counter.to_decimal(&mut dec_buf).unwrap();
        assert_eq!(&dec_buf[..dec_len], b"16");

        assert_eq!(counter.digit_count(), 2);
    }

    #[test]
    fn test_count_to_256() {
        let mut counter = CascadingHexCounter::new();

        for _ in 0..256 {
            counter.increment().unwrap();
        }

        let mut hex_buf = [0u8; 10];
        let hex_len = counter.to_hex(&mut hex_buf).unwrap();
        assert_eq!(&hex_buf[..hex_len], b"100");

        let mut dec_buf = [0u8; 10];
        let dec_len = counter.to_decimal(&mut dec_buf).unwrap();
        assert_eq!(&dec_buf[..dec_len], b"256");

        assert_eq!(counter.digit_count(), 3);
    }

    #[test]
    fn test_count_to_1000() {
        let mut counter = CascadingHexCounter::new();

        for _ in 0..1000 {
            counter.increment().unwrap();
        }

        let mut hex_buf = [0u8; 10];
        let hex_len = counter.to_hex(&mut hex_buf).unwrap();
        assert_eq!(&hex_buf[..hex_len], b"3E8");

        let mut dec_buf = [0u8; 10];
        let dec_len = counter.to_decimal(&mut dec_buf).unwrap();
        assert_eq!(&dec_buf[..dec_len], b"1000");
    }

    #[test]
    fn test_tier_promotion() {
        let mut counter = CascadingHexCounter::new();

        // Fill Tier 0 (4 digits)
        counter.buffer_tier_0 = [b'F'; TIER_0_CAPACITY];
        counter.digit_count = 4;
        assert_eq!(counter.current_tier(), 0);

        // Increment should promote to Tier 1
        counter.increment().unwrap();
        assert_eq!(counter.current_tier(), 1);

        let mut hex_buf = [0u8; 20];
        let hex_len = counter.to_hex(&mut hex_buf).unwrap();
        assert_eq!(&hex_buf[..hex_len], b"10000");

        let mut dec_buf = [0u8; 20];
        let dec_len = counter.to_decimal(&mut dec_buf).unwrap();
        assert_eq!(&dec_buf[..dec_len], b"65536");
    }

    #[test]
    fn test_reset() {
        let mut counter = CascadingHexCounter::new();

        for _ in 0..100 {
            counter.increment().unwrap();
        }

        let mut dec_buf = [0u8; 20];
        let dec_len = counter.to_decimal(&mut dec_buf).unwrap();
        assert_ne!(&dec_buf[..dec_len], b"0");

        counter.reset().unwrap();

        let mut hex_buf = [0u8; 10];
        let hex_len = counter.to_hex(&mut hex_buf).unwrap();
        assert_eq!(&hex_buf[..hex_len], b"0");

        let dec_len = counter.to_decimal(&mut dec_buf).unwrap();
        assert_eq!(&dec_buf[..dec_len], b"0");

        assert_eq!(counter.current_tier(), 0);
        assert_eq!(counter.digit_count(), 1);
    }

    #[test]
    fn test_hex_to_decimal_conversions() {
        let test_cases = [
            ("0", "0"),
            ("A", "10"),
            ("F", "15"),
            ("10", "16"),
            ("FF", "255"),
            ("100", "256"),
            ("3E8", "1000"),
            ("FFFF", "65535"),
        ];

        for (hex_input, expected_decimal) in test_cases.iter() {
            let mut counter = CascadingHexCounter::new();

            // Set counter to hex value by incrementing
            let target = u32::from_str_radix(hex_input, 16).unwrap();
            for _ in 0..target {
                counter.increment().unwrap();
            }

            let mut hex_buf = [0u8; 20];
            let hex_len = counter.to_hex(&mut hex_buf).unwrap();
            assert_eq!(&hex_buf[..hex_len], hex_input.as_bytes());

            let mut dec_buf = [0u8; 20];
            let dec_len = counter.to_decimal(&mut dec_buf).unwrap();
            assert_eq!(&dec_buf[..dec_len], expected_decimal.as_bytes());
        }
    }

    #[test]
    fn test_large_count() {
        let mut counter = CascadingHexCounter::new();

        let count = 100_000;
        for _ in 0..count {
            counter.increment().unwrap();
        }

        let mut hex_buf = [0u8; 20];
        let hex_len = counter.to_hex(&mut hex_buf).unwrap();
        assert_eq!(&hex_buf[..hex_len], b"186A0");

        let mut dec_buf = [0u8; 20];
        let dec_len = counter.to_decimal(&mut dec_buf).unwrap();
        assert_eq!(&dec_buf[..dec_len], b"100000");
    }

    #[test]
    fn test_char_conversions() {
        // Test hex_char_to_value
        assert_eq!(CascadingHexCounter::hex_char_to_value(b'0'), Some(0));
        assert_eq!(CascadingHexCounter::hex_char_to_value(b'9'), Some(9));
        assert_eq!(CascadingHexCounter::hex_char_to_value(b'A'), Some(10));
        assert_eq!(CascadingHexCounter::hex_char_to_value(b'F'), Some(15));
        assert_eq!(CascadingHexCounter::hex_char_to_value(b'G'), None);

        // Test value_to_hex_char
        assert_eq!(CascadingHexCounter::value_to_hex_char(0), Some(b'0'));
        assert_eq!(CascadingHexCounter::value_to_hex_char(9), Some(b'9'));
        assert_eq!(CascadingHexCounter::value_to_hex_char(10), Some(b'A'));
        assert_eq!(CascadingHexCounter::value_to_hex_char(15), Some(b'F'));
        assert_eq!(CascadingHexCounter::value_to_hex_char(16), None);
    }

    #[test]
    fn test_buffer_too_small() {
        let mut counter = CascadingHexCounter::new();

        for _ in 0..1000 {
            counter.increment().unwrap();
        }

        // Buffer too small for hex (needs 3 bytes for "3E8")
        let mut small_buf = [0u8; 2];
        assert!(counter.to_hex(&mut small_buf).is_err());

        // Buffer too small for decimal (needs 4 bytes for "1000")
        let mut small_buf = [0u8; 3];
        assert!(counter.to_decimal(&mut small_buf).is_err());
    }
}

// // ============================================================================
// // DEMONSTRATION
// // ============================================================================

// fn main() -> Result<()> {
//     println!("\n╔══════════════════════════════════════════════════════════════╗");
//     println!("║ Ribbon: \"It's tape all the way down.\"                       ║");
//     println!("║ Cascading Hex Counter - Zero-Heap Version                   ║");
//     println!("╚══════════════════════════════════════════════════════════════╝\n");

//     let mut counter = CascadingHexCounter::new();

//     // Pre-allocate buffers on stack
//     let mut hex_buffer = [0u8; 100];
//     let mut dec_buffer = [0u8; 100];

//     println!("Counting to 1000...\n");

//     for i in 0..=1000 {
//         if i == 1 || i == 10 || i == 100 || i == 256 || i == 1000 {
//             let hex_len = counter.to_hex(&mut hex_buffer)?;
//             let dec_len = counter.to_decimal(&mut dec_buffer)?;

//             let hex_str = std::str::from_utf8(&hex_buffer[..hex_len]).unwrap_or("<invalid utf8>");
//             let dec_str = std::str::from_utf8(&dec_buffer[..dec_len]).unwrap_or("<invalid utf8>");

//             println!("  Count: {} (hex: 0x{}, decimal: {})", i, hex_str, dec_str);
//         }

//         if i < 1000 {
//             counter.increment()?;
//         }
//     }

//     let dec_len = counter.to_decimal(&mut dec_buffer)?;
//     let dec_str = std::str::from_utf8(&dec_buffer[..dec_len]).unwrap_or("<invalid utf8>");

//     println!("\n✓ Demonstration complete");
//     println!("  Final count: {}", dec_str);
//     println!("  Active tier: {}", counter.current_tier());
//     println!("  Hex digits: {}", counter.digit_count());

//     // dir read test
//     let mut counter = CascadingHexCounter::new();

//     // Count items in directory
//     for entry in std::fs::read_dir(".")? {
//         let _ = entry?;
//         counter.increment()?;
//     }

//     let dec_len = counter.to_decimal(&mut dec_buffer)?;
//     let dec_str = std::str::from_utf8(&dec_buffer[..dec_len]).unwrap_or("<invalid utf8>");

//     println!("\ncwd count test:");
//     println!("decimal count: {}", dec_str);

//     Ok(())
// }
