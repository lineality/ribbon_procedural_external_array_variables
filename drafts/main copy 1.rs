//! # Procedural External Hex Cascade Counter
//!
//! A tiered stack-based hexadecimal counter that uses cascading buffers
//! for optimal memory efficiency while maintaining stack allocation benefits.
//!
//! ## Architecture
//! - Tier 0: 32 bytes (handles most real-world counts)
//! - Tier 1: 256 bytes (handles large counts)
//! - Tier 2: 2048 bytes (handles enormous counts)
//!
//! ## Memory Strategy
//! Start with smallest buffer, only promote to larger tiers when necessary.
//! OS lazy-commits memory pages, so unused tiers don't consume physical RAM.

use std::io::{Error, ErrorKind, Result};

/// Maximum capacity of the small buffer tier (Tier 0)
const TIER_0_CAPACITY: usize = 32;

/// Maximum capacity of the medium buffer tier (Tier 1)
const TIER_1_CAPACITY: usize = 256;

/// Maximum capacity of the large buffer tier (Tier 2)
const TIER_2_CAPACITY: usize = 2048;

/// Identifies which buffer tier is currently active
///
/// The counter starts in Tier 0 and promotes to higher tiers
/// only when the current tier's capacity is exhausted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ActiveTier {
    /// Small buffer (32 bytes) - handles 0 to 32 hex digits
    Tier0,
    /// Medium buffer (256 bytes) - handles 33 to 256 hex digits
    Tier1,
    /// Large buffer (2048 bytes) - handles 257 to 2048 hex digits
    Tier2,
}

impl ActiveTier {
    /// Get the capacity in bytes of this tier
    ///
    /// # Returns
    /// Number of hex digit characters this tier can store
    fn capacity(&self) -> usize {
        match self {
            ActiveTier::Tier0 => TIER_0_CAPACITY,
            ActiveTier::Tier1 => TIER_1_CAPACITY,
            ActiveTier::Tier2 => TIER_2_CAPACITY,
        }
    }

    /// Get the next higher tier
    ///
    /// # Returns
    /// - `Some(next_tier)` if there is a higher tier available
    /// - `None` if this is already the highest tier
    fn next_tier(&self) -> Option<ActiveTier> {
        match self {
            ActiveTier::Tier0 => Some(ActiveTier::Tier1),
            ActiveTier::Tier1 => Some(ActiveTier::Tier2),
            ActiveTier::Tier2 => None, // No higher tier available
        }
    }
}

/// Tiered stack-based hexadecimal counter with cascading buffers
///
/// # Memory Architecture
/// Three pre-allocated buffers on the stack:
/// - `buffer_tier_0`: 32 bytes (used first, most common case)
/// - `buffer_tier_1`: 256 bytes (used when Tier 0 is full)
/// - `buffer_tier_2`: 2048 bytes (used when Tier 1 is full)
///
/// # Storage Format
/// Hex digits stored as ASCII characters: '0'-'9', 'A'-'F'
/// Digits arranged right-to-left (rightmost is least significant)
///
/// # Example Layout (Tier 0, value 0xFF):
/// ```text
/// buffer_tier_0: [0, 0, 0, ..., 0, 'F', 'F']
///                                      ^---- length=2 digits
/// ```
///
/// # Policy
/// - Always use the smallest tier that fits the current value
/// - Promote to next tier only when carry would exceed capacity
/// - Never demote (once promoted, stay in higher tier)
/// - All three buffers always allocated on stack (but OS lazy-commits pages)
///
/// # Space Efficiency
/// Hex encoding: 4 bits of information per byte (50% efficient vs raw binary)
/// But much better than decimal (3.32 bits/byte) or binary (1 bit/byte)
pub struct TieredStackHexCounter {
    /// Small buffer for common cases (32 hex digits)
    ///
    /// Can represent values from 0x0 to 0xFFFFFFFF... (32 F's)
    /// This covers 0 to ~10^38 (larger than u128::MAX)
    buffer_tier_0: [u8; TIER_0_CAPACITY],

    /// Medium buffer for larger counts (256 hex digits)
    ///
    /// Can represent values from 0x0 to 0xFFFF... (256 F's)
    /// This covers 0 to ~10^308
    buffer_tier_1: [u8; TIER_1_CAPACITY],

    /// Large buffer for enormous counts (2048 hex digits)
    ///
    /// Can represent values from 0x0 to 0xFFFF... (2048 F's)
    /// This covers 0 to ~10^2466 (far more than needed for any practical use)
    buffer_tier_2: [u8; TIER_2_CAPACITY],

    /// Which buffer tier is currently active
    ///
    /// Determines which of the three buffers is being used for storage
    current_tier: ActiveTier,

    /// Number of valid hex digits in the active buffer (counted from right)
    ///
    /// Valid digits occupy the rightmost positions of the buffer.
    /// Example: length=3 means the rightmost 3 bytes contain valid hex digits.
    ///
    /// # Invariant
    /// Must always satisfy: 1 <= digit_count <= current_tier.capacity()
    digit_count: usize,
}

impl TieredStackHexCounter {
    /// Create a new tiered hex counter initialized to zero
    ///
    /// # Initial State
    /// - Starts in Tier 0 (smallest buffer)
    /// - Initialized to "0" (single hex digit)
    /// - Other tiers pre-allocated but untouched (OS won't commit pages yet)
    ///
    /// # Memory Layout After Creation
    /// ```text
    /// Stack frame: 2336 bytes allocated (32 + 256 + 2048)
    /// OS commitment: ~4KB page containing Tier 0 (lazy allocation)
    /// Tier 1 and 2 pages: Not yet committed by OS
    /// ```
    ///
    /// # Example
    /// ```
    /// let counter = TieredStackHexCounter::new();
    /// assert_eq!(counter.read().unwrap(), "0");
    /// ```
    pub fn new() -> Self {
        // Initialize small buffer with '0' at rightmost position
        let mut buffer_small = [0u8; TIER_0_CAPACITY];
        buffer_small[TIER_0_CAPACITY - 1] = b'0';

        TieredStackHexCounter {
            buffer_tier_0: buffer_small,
            buffer_tier_1: [0u8; TIER_1_CAPACITY], // Zeroed, not yet touched
            buffer_tier_2: [0u8; TIER_2_CAPACITY], // Zeroed, not yet touched
            current_tier: ActiveTier::Tier0,
            digit_count: 1, // Single '0' digit
        }
    }

    /// Get immutable reference to the currently active buffer
    ///
    /// # Returns
    /// Slice containing all bytes of the active tier's buffer
    ///
    /// # Note
    /// Only the rightmost `digit_count` bytes contain valid hex digits.
    /// Use `get_valid_digit_slice()` to get only the valid portion.
    fn get_active_buffer_reference(&self) -> &[u8] {
        match self.current_tier {
            ActiveTier::Tier0 => &self.buffer_tier_0[..],
            ActiveTier::Tier1 => &self.buffer_tier_1[..],
            ActiveTier::Tier2 => &self.buffer_tier_2[..],
        }
    }

    /// Get mutable reference to the currently active buffer
    ///
    /// # Returns
    /// Mutable slice containing all bytes of the active tier's buffer
    ///
    /// # Safety (Borrowing)
    /// This takes a mutable borrow of `self`, preventing access to other fields
    /// until the borrow is released. Store needed values before calling.
    fn get_active_buffer_mutable(&mut self) -> &mut [u8] {
        match self.current_tier {
            ActiveTier::Tier0 => &mut self.buffer_tier_0[..],
            ActiveTier::Tier1 => &mut self.buffer_tier_1[..],
            ActiveTier::Tier2 => &mut self.buffer_tier_2[..],
        }
    }

    /// Get the slice containing only valid hex digits (from active buffer)
    ///
    /// # Returns
    /// Slice of the rightmost `digit_count` bytes, which contain the actual value
    ///
    /// # Example
    /// ```text
    /// Buffer: [0, 0, 0, ..., 0, 'F', 'F', 'A', '3']
    ///                               ^-----------^  <- This slice (digit_count=4)
    /// Represents: 0xFF A3
    /// ```
    fn get_valid_digit_slice(&self) -> &[u8] {
        let buffer_capacity = self.current_tier.capacity();
        let start_index = buffer_capacity - self.digit_count;
        let buffer = self.get_active_buffer_reference();
        &buffer[start_index..buffer_capacity]
    }

    /// Promote counter to the next higher tier
    ///
    /// # Process
    /// 1. Verify next tier is available
    /// 2. Calculate positions in old and new buffers
    /// 3. Copy valid digits from current buffer to new buffer
    /// 4. Update `current_tier` to point to new buffer
    ///
    /// # Errors
    /// Returns `OutOfMemory` error if already at highest tier (Tier 2)
    ///
    /// # Memory Behavior
    /// When promoting, this is typically the first write to the new buffer,
    /// causing the OS to commit the physical memory pages for that buffer.
    ///
    /// # Example
    /// ```text
    /// Before promotion (Tier 0 → Tier 1):
    ///   Tier 0: [0, 0, ..., 'F', 'F'] (capacity=32, length=2)
    ///   Tier 1: [0, 0, ..., 0, 0] (capacity=256, untouched)
    ///
    /// After promotion:
    ///   Tier 0: [0, 0, ..., 'F', 'F'] (unchanged, no longer active)
    ///   Tier 1: [0, 0, ..., 'F', 'F'] (capacity=256, length=2, active)
    ///   current_tier: Tier1
    /// ```
    fn promote_to_next_tier(&mut self) -> Result<()> {
        // Determine if promotion is possible
        let next_tier = self.current_tier.next_tier().ok_or_else(|| {
            Error::new(
                ErrorKind::OutOfMemory,
                format!(
                    "Cannot promote beyond Tier 2: counter has reached maximum capacity of {} hex digits",
                    TIER_2_CAPACITY
                ),
            )
        })?;

        // Calculate buffer positions
        let old_capacity = self.current_tier.capacity();
        let new_capacity = next_tier.capacity();
        let start_index_old = old_capacity - self.digit_count;
        let start_index_new = new_capacity - self.digit_count;

        // Copy valid digits from old buffer to new buffer
        // We must do this carefully to avoid borrowing conflicts
        match self.current_tier {
            ActiveTier::Tier0 => {
                // Copying from Tier 0 to Tier 1
                let digits_to_copy = &self.buffer_tier_0[start_index_old..old_capacity];
                self.buffer_tier_1[start_index_new..new_capacity].copy_from_slice(digits_to_copy);
            }
            ActiveTier::Tier1 => {
                // Copying from Tier 1 to Tier 2
                let digits_to_copy = &self.buffer_tier_1[start_index_old..old_capacity];
                self.buffer_tier_2[start_index_new..new_capacity].copy_from_slice(digits_to_copy);
            }
            ActiveTier::Tier2 => {
                // Should never reach here due to earlier check
                unreachable!("Cannot promote beyond Tier 2");
            }
        }

        // Update to use new tier
        self.current_tier = next_tier;

        Ok(())
    }

    /// Convert ASCII hex character to numeric value (0-15)
    ///
    /// # Arguments
    /// * `hex_character` - ASCII character ('0'-'9', 'A'-'F', 'a'-'f')
    ///
    /// # Returns
    /// - `Some(value)` where value is 0-15 if valid hex character
    /// - `None` if character is not a valid hex digit
    ///
    /// # Examples
    /// - '0' → Some(0)
    /// - '9' → Some(9)
    /// - 'A' or 'a' → Some(10)
    /// - 'F' or 'f' → Some(15)
    /// - 'G' → None (invalid)
    fn hex_char_to_numeric_value(hex_character: u8) -> Option<u8> {
        match hex_character {
            b'0'..=b'9' => Some(hex_character - b'0'),
            b'A'..=b'F' => Some(hex_character - b'A' + 10),
            b'a'..=b'f' => Some(hex_character - b'a' + 10),
            _ => None, // Invalid hex character
        }
    }

    /// Convert numeric value (0-15) to uppercase ASCII hex character
    ///
    /// # Arguments
    /// * `numeric_value` - Value from 0 to 15
    ///
    /// # Returns
    /// - `Some(character)` if value is 0-15
    /// - `None` if value is outside valid range
    ///
    /// # Examples
    /// - 0 → Some('0')
    /// - 9 → Some('9')
    /// - 10 → Some('A')
    /// - 15 → Some('F')
    /// - 16 → None (invalid)
    fn numeric_value_to_hex_char(numeric_value: u8) -> Option<u8> {
        match numeric_value {
            0..=9 => Some(b'0' + numeric_value),
            10..=15 => Some(b'A' + numeric_value - 10),
            _ => None, // Value too large for hex digit
        }
    }

    /// Increment the counter by one
    ///
    /// # Algorithm
    /// Implements standard base-16 addition with carry propagation:
    ///
    /// 1. Start with rightmost digit (least significant)
    /// 2. Add 1, check if result >= 16 (carry condition)
    /// 3. If carry: set digit to 0, continue to next digit left
    /// 4. If no carry: set digit to new value, done
    /// 5. If carry reaches leftmost digit and continues: need to add new digit
    /// 6. If new digit would exceed capacity: promote to next tier
    ///
    /// # Edge Cases
    /// - Single digit '0' → '1' (no carry)
    /// - Single digit 'F' → '10' (carry, extend left)
    /// - All 'F's → '10...0' (carry propagates to new digit)
    /// - Buffer full → promote to next tier, then add digit
    ///
    /// # Errors
    /// Returns error if:
    /// - Invalid hex digit found in buffer (data corruption)
    /// - Already at maximum tier and capacity (cannot grow further)
    ///
    /// # Performance
    /// - Best case: O(1) - rightmost digit is not F
    /// - Worst case: O(n) - all digits are F, must process all + extend
    /// - Amortized: O(1) - carry propagation is rare
    pub fn increment(&mut self) -> Result<()> {
        // Store values we'll need before taking mutable borrow
        // This avoids borrow checker conflicts
        let buffer_capacity = self.current_tier.capacity();
        let current_digit_count = self.digit_count;
        let start_index = buffer_capacity - current_digit_count;

        // Check if we have room to potentially add a digit (for carry)
        let can_extend_in_current_tier = current_digit_count < buffer_capacity;

        // Get mutable access to buffer
        // After this point, cannot access self.field until borrow ends
        let active_buffer = self.get_active_buffer_mutable();

        // Carry flag: starts as 1 (we're adding 1)
        let mut carry_value = 1u8;

        // Process digits from right to left (bounded loop)
        for loop_index in 0..current_digit_count {
            // Calculate actual buffer index (right to left)
            let buffer_index = buffer_capacity - 1 - loop_index;

            // Only process if we still have a carry
            if carry_value > 0 {
                // Convert ASCII hex character to numeric value
                let current_digit_value = Self::hex_char_to_numeric_value(
                    active_buffer[buffer_index],
                )
                .ok_or_else(|| {
                    Error::new(
                        ErrorKind::InvalidData,
                        format!(
                            "Invalid hex digit 0x{:02X} found at buffer position {}",
                            active_buffer[buffer_index], buffer_index
                        ),
                    )
                })?;

                // Add carry to current digit
                let mut new_digit_value = current_digit_value + carry_value;

                // Check for carry to next position
                if new_digit_value >= 16 {
                    new_digit_value = 0; // Wrap to 0
                    carry_value = 1; // Carry continues
                } else {
                    carry_value = 0; // No more carry
                }

                // Convert back to ASCII hex character
                let new_hex_char =
                    Self::numeric_value_to_hex_char(new_digit_value).ok_or_else(|| {
                        Error::new(
                            ErrorKind::InvalidData,
                            format!(
                                "Failed to convert numeric value {} to hex character",
                                new_digit_value
                            ),
                        )
                    })?;

                // Store new digit
                active_buffer[buffer_index] = new_hex_char;
            } else {
                // No carry, we're done
                break;
            }
        }

        // Release mutable borrow of buffer
        // Now we can access self.field again
        drop(active_buffer);

        // If still carrying after processing all digits, need to add new digit
        if carry_value > 0 {
            if can_extend_in_current_tier {
                // Room in current tier: add digit to the left
                let new_start_index = start_index - 1;
                let buffer_again = self.get_active_buffer_mutable();
                buffer_again[new_start_index] = b'1';
                drop(buffer_again);
                self.digit_count += 1;
            } else {
                // Current tier is full: must promote to next tier
                self.promote_to_next_tier()?;

                // After promotion, add the carry digit
                let new_capacity = self.current_tier.capacity();
                let new_start_index = new_capacity - self.digit_count - 1;
                let new_buffer = self.get_active_buffer_mutable();
                new_buffer[new_start_index] = b'1';
                drop(new_buffer);
                self.digit_count += 1;
            }
        }

        Ok(())
    }

    /// Read the current counter value as a hexadecimal string
    ///
    /// # Returns
    /// Uppercase hex string (e.g., "0", "FF", "10A3", "DEADBEEF")
    ///
    /// # Errors
    /// Returns error if buffer contains invalid UTF-8 (should never happen)
    ///
    /// # Example
    /// ```
    /// let mut counter = TieredStackHexCounter::new();
    /// counter.increment()?;
    /// assert_eq!(counter.read()?, "1");
    /// ```
    pub fn read(&self) -> Result<String> {
        let valid_digits = self.get_valid_digit_slice();
        String::from_utf8(valid_digits.to_vec()).map_err(|utf8_error| {
            Error::new(
                ErrorKind::InvalidData,
                format!("Buffer contains invalid UTF-8 data: {}", utf8_error),
            )
        })
    }

    /// Reset counter to zero
    ///
    /// # Process
    /// 1. Clear Tier 0 buffer
    /// 2. Set rightmost byte to '0'
    /// 3. Reset to Tier 0
    /// 4. Set digit count to 1
    ///
    /// # Note
    /// Does not clear Tier 1 and Tier 2 buffers (unnecessary, they're inactive)
    pub fn reset(&mut self) -> Result<()> {
        // Reset to Tier 0 with single '0' digit
        self.buffer_tier_0 = [0u8; TIER_0_CAPACITY];
        self.buffer_tier_0[TIER_0_CAPACITY - 1] = b'0';
        self.current_tier = ActiveTier::Tier0;
        self.digit_count = 1;
        Ok(())
    }

    /// Get comprehensive memory usage statistics
    ///
    /// # Returns
    /// Tuple of (total_allocated, currently_used, tier, tier_capacity, wasted_bytes)
    ///
    /// - `total_allocated`: Total bytes allocated on stack (all 3 tiers)
    /// - `currently_used`: Bytes actually storing valid hex digits
    /// - `tier`: Which tier is active (0, 1, or 2)
    /// - `tier_capacity`: Capacity of active tier in bytes
    /// - `wasted_bytes`: Unused bytes in active tier
    pub fn get_memory_statistics(&self) -> (usize, usize, u8, usize, usize) {
        let total_allocated_bytes = TIER_0_CAPACITY + TIER_1_CAPACITY + TIER_2_CAPACITY;
        let bytes_currently_used = self.digit_count;
        let tier_number = match self.current_tier {
            ActiveTier::Tier0 => 0,
            ActiveTier::Tier1 => 1,
            ActiveTier::Tier2 => 2,
        };
        let active_tier_capacity = self.current_tier.capacity();
        let wasted_bytes_in_active_tier = active_tier_capacity - bytes_currently_used;

        (
            total_allocated_bytes,
            bytes_currently_used,
            tier_number,
            active_tier_capacity,
            wasted_bytes_in_active_tier,
        )
    }

    /// Print detailed memory usage report to stdout
    ///
    /// Displays:
    /// - Total stack allocation
    /// - Active tier and its capacity
    /// - Actual bytes used
    /// - Wasted bytes (and percentage)
    /// - Maximum representable value
    pub fn print_memory_report(&self) {
        let (total_allocated, bytes_used, tier_num, tier_capacity, wasted) =
            self.get_memory_statistics();

        let waste_percentage = (wasted as f64 / tier_capacity as f64) * 100.0;

        println!("  ╔══════════════════════════════════════════════════════════╗");
        println!("  ║ Memory Usage Report                                      ║");
        println!("  ╚══════════════════════════════════════════════════════════╝");
        println!("    Total stack allocation: {} bytes", total_allocated);
        println!(
            "    Active tier: Tier {} (capacity: {} bytes)",
            tier_num, tier_capacity
        );
        println!("    Bytes actually used: {} bytes", bytes_used);
        println!(
            "    Wasted in active tier: {} bytes ({:.1}%)",
            wasted, waste_percentage
        );
        println!("    Current value length: {} hex digits", bytes_used);
        println!(
            "    Can represent up to: 16^{} ≈ 2^{} ≈ 10^{}",
            bytes_used,
            bytes_used * 4,
            (bytes_used as f64 * 4.0 * 0.30103) as usize // log10(2) ≈ 0.30103
        );
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Test basic creation and initial state
    #[test]
    fn test_counter_creation_and_initial_state() {
        let counter = TieredStackHexCounter::new();

        // Should start with "0"
        assert_eq!(counter.read().unwrap(), "0");

        // Should be in Tier 0
        let (_, _, tier, _, _) = counter.get_memory_statistics();
        assert_eq!(tier, 0);

        // Should have 1 digit
        assert_eq!(counter.digit_count, 1);
    }

    /// Test increment from 0 to 15 (single hex digit)
    #[test]
    fn test_increment_single_digit_sequence() {
        let mut counter = TieredStackHexCounter::new();

        let expected_sequence = [
            "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "A", "B", "C", "D", "E", "F",
        ];

        for expected_value in expected_sequence.iter() {
            assert_eq!(counter.read().unwrap(), *expected_value);
            counter.increment().unwrap();
        }
    }

    /// Test carry from F to 10 (extending to two digits)
    #[test]
    fn test_carry_to_two_digits() {
        let mut counter = TieredStackHexCounter::new();

        // Count to 16 (0x10)
        for _ in 0..16 {
            counter.increment().unwrap();
        }

        assert_eq!(counter.read().unwrap(), "10");
        assert_eq!(counter.digit_count, 2);
    }

    /// Test counting to 256 (0x100)
    #[test]
    fn test_count_to_256() {
        let mut counter = TieredStackHexCounter::new();

        for _ in 0..256 {
            counter.increment().unwrap();
        }

        assert_eq!(counter.read().unwrap(), "100");
        assert_eq!(counter.digit_count, 3);
    }

    /// Test reset functionality
    #[test]
    fn test_reset_after_counting() {
        let mut counter = TieredStackHexCounter::new();

        // Count to 100
        for _ in 0..100 {
            counter.increment().unwrap();
        }

        // Verify we're not at zero
        assert_ne!(counter.read().unwrap(), "0");

        // Reset
        counter.reset().unwrap();

        // Should be back to "0"
        assert_eq!(counter.read().unwrap(), "0");
        assert_eq!(counter.digit_count, 1);
    }

    /// Test tier promotion from Tier 0 to Tier 1
    #[test]
    fn test_tier_0_to_tier_1_promotion() {
        let mut counter = TieredStackHexCounter::new();

        // Fill Tier 0 (32 digits of all F's)
        // Value will be: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
        // That's 2^128 - 1, but we can go beyond that

        // Create a counter with 32 F's
        counter.buffer_tier_0 = [b'F'; TIER_0_CAPACITY];
        counter.digit_count = 32;

        // Verify we're in Tier 0
        let (_, _, tier, _, _) = counter.get_memory_statistics();
        assert_eq!(tier, 0);

        // Increment (should promote to Tier 1)
        counter.increment().unwrap();

        // Verify promotion to Tier 1
        let (_, _, tier, _, _) = counter.get_memory_statistics();
        assert_eq!(tier, 1);

        // Verify value is correct (should be 1000...0 with 33 digits)
        let value = counter.read().unwrap();
        assert_eq!(value.len(), 33);
        assert!(value.starts_with('1'));
        assert!(value[1..].chars().all(|c| c == '0'));
    }

    /// Test hex character conversion functions
    #[test]
    fn test_hex_character_conversions() {
        // Test numeric to hex char
        assert_eq!(
            TieredStackHexCounter::numeric_value_to_hex_char(0),
            Some(b'0')
        );
        assert_eq!(
            TieredStackHexCounter::numeric_value_to_hex_char(9),
            Some(b'9')
        );
        assert_eq!(
            TieredStackHexCounter::numeric_value_to_hex_char(10),
            Some(b'A')
        );
        assert_eq!(
            TieredStackHexCounter::numeric_value_to_hex_char(15),
            Some(b'F')
        );
        assert_eq!(TieredStackHexCounter::numeric_value_to_hex_char(16), None);

        // Test hex char to numeric
        assert_eq!(
            TieredStackHexCounter::hex_char_to_numeric_value(b'0'),
            Some(0)
        );
        assert_eq!(
            TieredStackHexCounter::hex_char_to_numeric_value(b'9'),
            Some(9)
        );
        assert_eq!(
            TieredStackHexCounter::hex_char_to_numeric_value(b'A'),
            Some(10)
        );
        assert_eq!(
            TieredStackHexCounter::hex_char_to_numeric_value(b'a'),
            Some(10)
        );
        assert_eq!(
            TieredStackHexCounter::hex_char_to_numeric_value(b'F'),
            Some(15)
        );
        assert_eq!(
            TieredStackHexCounter::hex_char_to_numeric_value(b'f'),
            Some(15)
        );
        assert_eq!(TieredStackHexCounter::hex_char_to_numeric_value(b'G'), None);
    }

    /// Test memory statistics reporting
    #[test]
    fn test_memory_statistics_accuracy() {
        let mut counter = TieredStackHexCounter::new();

        // Initial state
        let (total, used, tier, capacity, wasted) = counter.get_memory_statistics();
        assert_eq!(total, TIER_0_CAPACITY + TIER_1_CAPACITY + TIER_2_CAPACITY);
        assert_eq!(used, 1); // Single '0' digit
        assert_eq!(tier, 0);
        assert_eq!(capacity, TIER_0_CAPACITY);
        assert_eq!(wasted, TIER_0_CAPACITY - 1);

        // After counting to 256
        for _ in 0..256 {
            counter.increment().unwrap();
        }

        let (total2, used2, tier2, capacity2, _) = counter.get_memory_statistics();
        assert_eq!(total2, total); // Total allocation unchanged
        assert_eq!(used2, 3); // "100" = 3 digits
        assert_eq!(tier2, 0); // Still in Tier 0 (fits in 32 bytes)
        assert_eq!(capacity2, TIER_0_CAPACITY);
    }

    /// Test that all three tiers are reachable
    #[test]
    fn test_all_tiers_reachable() {
        let mut counter = TieredStackHexCounter::new();

        // Start in Tier 0
        let (_, _, tier, _, _) = counter.get_memory_statistics();
        assert_eq!(tier, 0);

        // Force to Tier 1
        counter.buffer_tier_0 = [b'F'; TIER_0_CAPACITY];
        counter.digit_count = TIER_0_CAPACITY;
        counter.increment().unwrap();

        let (_, _, tier, _, _) = counter.get_memory_statistics();
        assert_eq!(tier, 1);

        // Force to Tier 2
        counter.buffer_tier_1 = [b'F'; TIER_1_CAPACITY];
        counter.digit_count = TIER_1_CAPACITY;
        counter.increment().unwrap();

        let (_, _, tier, _, _) = counter.get_memory_statistics();
        assert_eq!(tier, 2);
    }

    /// Test error handling when exceeding maximum capacity
    #[test]
    fn test_maximum_capacity_error() {
        let mut counter = TieredStackHexCounter::new();

        // Force to Tier 2 at maximum capacity
        counter.current_tier = ActiveTier::Tier2;
        counter.buffer_tier_2 = [b'F'; TIER_2_CAPACITY];
        counter.digit_count = TIER_2_CAPACITY;

        // Attempt to increment beyond maximum capacity
        let result = counter.increment();

        // Should return error
        assert!(result.is_err());

        // Verify error is OutOfMemory
        if let Err(error) = result {
            assert_eq!(error.kind(), ErrorKind::OutOfMemory);
        }
    }
}

/// Demonstration and testing entry point
fn main() -> Result<()> {
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║  Procedural External Hex Cascade Counter                    ║");
    println!("║  Tiered Stack-Based Arbitrary Precision Counter             ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    // Create and demonstrate counter
    let mut counter = TieredStackHexCounter::new();

    println!("Initial state:");
    println!("  Value: 0x{}", counter.read()?);
    counter.print_memory_report();

    // Count to a reasonable test value
    let test_count = 1000;
    println!("\n\nCounting to {}...", test_count);

    for iteration in 0..test_count {
        counter.increment()?;

        // Report tier changes
        let (_, _, current_tier, _, _) = counter.get_memory_statistics();
        if iteration == 15 {
            println!("current_tier -> {current_tier}");
            println!("\n  After 16 increments (entering 2-digit hex):");
            println!("  Value: 0x{}", counter.read()?);
        }
        if iteration == 255 {
            println!("\n  After 256 increments (entering 3-digit hex):");
            println!("  Value: 0x{}", counter.read()?);
        }
    }

    println!("\n\nFinal state after {} increments:", test_count);
    println!("  Value: 0x{}", counter.read()?);
    counter.print_memory_report();

    // Test reset
    println!("\n\nTesting reset...");
    counter.reset()?;
    println!("  Value after reset: 0x{}", counter.read()?);

    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║  Demonstration Complete                                      ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    let mut counter = TieredStackHexCounter::new();

    // Count files in directory
    for entry in std::fs::read_dir(
        "/home/oops/code/gutenberg_babble/perseids/byte_perseid/pseudo_toml_maker_training_data/toml_production_output_60000v2",
    )? {
        let _ = entry?;
        counter.increment()?;
    }

    println!("Count: 0x{}", counter.read()?);
    counter.print_memory_report();

    Ok(())
}
