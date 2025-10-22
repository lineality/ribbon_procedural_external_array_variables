//! # Hybrid Counter: Native Integers First, Hex Buffer Fallback
//!
//! ## Architecture Philosophy
//! Use the fastest method appropriate to the count size:
//! - Stage 0: u8 (0 to 255) - CPU register, ~1ns per increment
//! - Stage 1: u16 (256 to 65,535) - CPU register, ~1ns per increment
//! - Stage 2: u32 (65,536 to 4,294,967,295) - CPU register, ~1-2ns per increment
//! - Stage 3: u64 (4B to 18 quintillion) - CPU register, ~1-2ns per increment
//! - Stage 4: Hex buffer (unlimited) - ~50-200ns per increment
//!
//! ## Policy: Restart on Overflow
//! When a stage overflows, we don't cascade - we restart with a fresh,
//! larger container. This is simpler and more robust since overflows are
//! rare exception-handling events.
//!
//! ## Memory Efficiency
//! Native integers use only what they need (1, 2, 4, or 8 bytes).
//! Buffer is only allocated if count exceeds u64::MAX.

use std::io::{Error, ErrorKind, Result};

/// Maximum capacity of hex buffer (when native integers overflow)
const HEX_BUFFER_CAPACITY: usize = 2048;

/// Current counting stage/strategy
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CountingStage {
    /// Using u8 (0 to 255)
    UsingU8,
    /// Using u16 (256 to 65,535)
    UsingU16,
    /// Using u32 (65,536 to 4,294,967,295)
    UsingU32,
    /// Using u64 (4B+ to 18 quintillion)
    UsingU64,
    /// Using hex buffer (unlimited, 2048 digits max)
    UsingHexBuffer,
}

impl CountingStage {
    /// Get human-readable name of this stage
    fn name(&self) -> &'static str {
        match self {
            CountingStage::UsingU8 => "u8 (native register)",
            CountingStage::UsingU16 => "u16 (native register)",
            CountingStage::UsingU32 => "u32 (native register)",
            CountingStage::UsingU64 => "u64 (native register)",
            CountingStage::UsingHexBuffer => "Hex buffer (arbitrary precision)",
        }
    }

    /// Get maximum value this stage can represent
    fn max_value_description(&self) -> &'static str {
        match self {
            CountingStage::UsingU8 => "255",
            CountingStage::UsingU16 => "65,535",
            CountingStage::UsingU32 => "4,294,967,295",
            CountingStage::UsingU64 => "18,446,744,073,709,551,615",
            CountingStage::UsingHexBuffer => "16^2048 (practically unlimited)",
        }
    }

    /// Get next stage when current overflows
    fn next_stage(&self) -> Option<CountingStage> {
        match self {
            CountingStage::UsingU8 => Some(CountingStage::UsingU16),
            CountingStage::UsingU16 => Some(CountingStage::UsingU32),
            CountingStage::UsingU32 => Some(CountingStage::UsingU64),
            CountingStage::UsingU64 => Some(CountingStage::UsingHexBuffer),
            CountingStage::UsingHexBuffer => None, // No higher stage
        }
    }
}

/// Hybrid counter: native integers first, hex buffer as fallback
///
/// # Memory Layout
/// Total stack allocation: 2056 bytes (always allocated, rarely used)
/// - Option<u8>: 2 bytes
/// - Option<u16>: 4 bytes
/// - Option<u32>: 8 bytes
/// - Option<u64>: 16 bytes
/// - [u8; 2048]: 2048 bytes (only touched if count > u64::MAX)
///
/// OS lazy-commits pages, so unused buffer doesn't consume physical RAM.
///
/// # Performance Characteristics
/// - u8/u16/u32/u64 stages: ~1-2 nanoseconds per increment (CPU register ops)
/// - Hex buffer stage: ~50-200 nanoseconds per increment (memory ops)
/// - Stage transitions: ~10-100 nanoseconds (rare exception events)
pub struct HybridCounter {
    /// Current counting stage
    current_stage: CountingStage,

    /// u8 counter (0 to 255)
    /// None if we've outgrown this stage
    counter_u8: Option<u8>,

    /// u16 counter (256 to 65,535)
    /// None if we've outgrown this stage
    counter_u16: Option<u16>,

    /// u32 counter (65,536 to 4 billion)
    /// None if we've outgrown this stage
    counter_u32: Option<u32>,

    /// u64 counter (4B+ to 18 quintillion)
    /// None if we've outgrown this stage
    counter_u64: Option<u64>,

    /// Hex buffer for unlimited counting (only used if exceeding u64::MAX)
    /// Digits stored as ASCII hex characters from right to left
    hex_buffer: [u8; HEX_BUFFER_CAPACITY],

    /// Number of valid hex digits in buffer (if using hex buffer stage)
    hex_digit_count: usize,
}

impl HybridCounter {
    /// Create new counter starting at zero
    ///
    /// # Initial State
    /// Starts in u8 stage (most efficient for small counts)
    ///
    /// # Example
    /// ```
    /// let counter = HybridCounter::new();
    /// assert_eq!(counter.read_decimal()?, "0");
    /// ```
    pub fn new() -> Self {
        let mut buffer = [0u8; HEX_BUFFER_CAPACITY];
        buffer[HEX_BUFFER_CAPACITY - 1] = b'0'; // Initialize rightmost to '0'

        HybridCounter {
            current_stage: CountingStage::UsingU8,
            counter_u8: Some(0),
            counter_u16: None,
            counter_u32: None,
            counter_u64: None,
            hex_buffer: buffer,
            hex_digit_count: 1,
        }
    }

    /// Promote to next stage when current overflows
    ///
    /// # Process (Restart Strategy)
    /// Instead of copying/cascading, we restart fresh:
    /// 1. Get current value as u128 (or hex if too large)
    /// 2. Clear current stage (set to None)
    /// 3. Initialize next stage with current value
    /// 4. Update current_stage marker
    ///
    /// # Why Restart Instead of Cascade?
    /// - Simpler logic (no complex copying)
    /// - Rare event (happens only at stage boundaries)
    /// - Clean state (no stale data in old stages)
    /// - Easier to debug and test
    ///
    /// # Errors
    /// Returns error if already at maximum stage (hex buffer full)
    fn promote_to_next_stage(&mut self) -> Result<()> {
        let next = self.current_stage.next_stage().ok_or_else(|| {
            Error::new(
                ErrorKind::OutOfMemory,
                format!(
                    "Counter has reached maximum capacity of {} hex digits",
                    HEX_BUFFER_CAPACITY
                ),
            )
        })?;

        // Get current value before clearing
        let current_value_for_transfer = match self.current_stage {
            CountingStage::UsingU8 => self.counter_u8.unwrap() as u128,
            CountingStage::UsingU16 => self.counter_u16.unwrap() as u128,
            CountingStage::UsingU32 => self.counter_u32.unwrap() as u128,
            CountingStage::UsingU64 => self.counter_u64.unwrap() as u128,
            CountingStage::UsingHexBuffer => {
                // Already at hex buffer, can't promote
                return Err(Error::new(
                    ErrorKind::OutOfMemory,
                    "Already using hex buffer, cannot promote further",
                ));
            }
        };

        // Clear current stage
        match self.current_stage {
            CountingStage::UsingU8 => self.counter_u8 = None,
            CountingStage::UsingU16 => self.counter_u16 = None,
            CountingStage::UsingU32 => self.counter_u32 = None,
            CountingStage::UsingU64 => self.counter_u64 = None,
            CountingStage::UsingHexBuffer => unreachable!(),
        }

        // Initialize next stage with current value
        match next {
            CountingStage::UsingU16 => {
                self.counter_u16 = Some(current_value_for_transfer as u16);
            }
            CountingStage::UsingU32 => {
                self.counter_u32 = Some(current_value_for_transfer as u32);
            }
            CountingStage::UsingU64 => {
                self.counter_u64 = Some(current_value_for_transfer as u64);
            }
            CountingStage::UsingHexBuffer => {
                // Convert u128 value to hex buffer
                self.initialize_hex_buffer_from_u128(current_value_for_transfer)?;
            }
            CountingStage::UsingU8 => unreachable!(), // Never promote to u8
        }

        // Update stage marker
        self.current_stage = next;

        Ok(())
    }

    /// Initialize hex buffer from a u128 value
    ///
    /// # Arguments
    /// * `value` - The u128 value to convert to hex representation
    ///
    /// # Process
    /// 1. Convert value to hex string
    /// 2. Store hex digits in buffer (right-aligned)
    /// 3. Update digit count
    fn initialize_hex_buffer_from_u128(&mut self, value: u128) -> Result<()> {
        // Convert to hex string
        let hex_string = format!("{:X}", value);
        let hex_bytes = hex_string.as_bytes();

        // Verify it fits in buffer
        if hex_bytes.len() > HEX_BUFFER_CAPACITY {
            return Err(Error::new(
                ErrorKind::InvalidData,
                format!(
                    "Value requires {} hex digits, but buffer only holds {}",
                    hex_bytes.len(),
                    HEX_BUFFER_CAPACITY
                ),
            ));
        }

        // Clear buffer and copy hex digits (right-aligned)
        self.hex_buffer = [0u8; HEX_BUFFER_CAPACITY];
        let start_index = HEX_BUFFER_CAPACITY - hex_bytes.len();
        self.hex_buffer[start_index..].copy_from_slice(hex_bytes);
        self.hex_digit_count = hex_bytes.len();

        Ok(())
    }

    /// Increment hex buffer by one
    ///
    /// # Algorithm
    /// Standard base-16 addition with carry propagation (same as before)
    fn increment_hex_buffer(&mut self) -> Result<()> {
        // Store values before working with buffer
        let buffer_capacity = HEX_BUFFER_CAPACITY;
        let current_digit_count = self.hex_digit_count;
        let start_index = buffer_capacity - current_digit_count;

        // Check if we can extend
        if current_digit_count >= buffer_capacity {
            return Err(Error::new(
                ErrorKind::OutOfMemory,
                "Hex buffer is full, cannot increment further",
            ));
        }

        let mut carry_value = 1u8;

        // Process digits right to left
        for loop_index in 0..current_digit_count {
            let buffer_index = buffer_capacity - 1 - loop_index;

            if carry_value > 0 {
                let current_digit_value = match self.hex_buffer[buffer_index] {
                    b'0'..=b'9' => self.hex_buffer[buffer_index] - b'0',
                    b'A'..=b'F' => self.hex_buffer[buffer_index] - b'A' + 10,
                    b'a'..=b'f' => self.hex_buffer[buffer_index] - b'a' + 10,
                    invalid_byte => {
                        return Err(Error::new(
                            ErrorKind::InvalidData,
                            format!(
                                "Invalid hex digit 0x{:02X} at position {}",
                                invalid_byte, buffer_index
                            ),
                        ));
                    }
                };

                let mut new_digit_value = current_digit_value + carry_value;

                if new_digit_value >= 16 {
                    new_digit_value = 0;
                    carry_value = 1;
                } else {
                    carry_value = 0;
                }

                self.hex_buffer[buffer_index] = match new_digit_value {
                    0..=9 => b'0' + new_digit_value,
                    10..=15 => b'A' + new_digit_value - 10,
                    _ => {
                        return Err(Error::new(
                            ErrorKind::InvalidData,
                            format!("Invalid hex value {} after increment", new_digit_value),
                        ));
                    }
                };
            } else {
                break;
            }
        }

        // If still carrying, add new digit
        if carry_value > 0 {
            if current_digit_count >= buffer_capacity {
                return Err(Error::new(
                    ErrorKind::OutOfMemory,
                    "Cannot add more digits, buffer is full",
                ));
            }

            let new_start_index = start_index - 1;
            self.hex_buffer[new_start_index] = b'1';
            self.hex_digit_count += 1;
        }

        Ok(())
    }

    /// Increment counter by one
    ///
    /// # Algorithm
    /// 1. Try to increment in current stage
    /// 2. If overflow detected, promote to next stage
    /// 3. Increment in new stage
    ///
    /// # Performance
    /// - Fast path (no overflow): 1-2 nanoseconds
    /// - Slow path (overflow): 10-200 nanoseconds (stage transition)
    ///
    /// # Errors
    /// Returns error if hex buffer is full and cannot grow further
    pub fn increment(&mut self) -> Result<()> {
        match self.current_stage {
            CountingStage::UsingU8 => {
                let current = self.counter_u8.unwrap();
                match current.checked_add(1) {
                    Some(new_value) => {
                        self.counter_u8 = Some(new_value);
                    }
                    None => {
                        // Overflow: promote to u16
                        self.promote_to_next_stage()?;
                        self.increment()?; // Retry in new stage
                    }
                }
            }
            CountingStage::UsingU16 => {
                let current = self.counter_u16.unwrap();
                match current.checked_add(1) {
                    Some(new_value) => {
                        self.counter_u16 = Some(new_value);
                    }
                    None => {
                        // Overflow: promote to u32
                        self.promote_to_next_stage()?;
                        self.increment()?; // Retry in new stage
                    }
                }
            }
            CountingStage::UsingU32 => {
                let current = self.counter_u32.unwrap();
                match current.checked_add(1) {
                    Some(new_value) => {
                        self.counter_u32 = Some(new_value);
                    }
                    None => {
                        // Overflow: promote to u64
                        self.promote_to_next_stage()?;
                        self.increment()?; // Retry in new stage
                    }
                }
            }
            CountingStage::UsingU64 => {
                let current = self.counter_u64.unwrap();
                match current.checked_add(1) {
                    Some(new_value) => {
                        self.counter_u64 = Some(new_value);
                    }
                    None => {
                        // Overflow: promote to hex buffer
                        self.promote_to_next_stage()?;
                        self.increment()?; // Retry in new stage
                    }
                }
            }
            CountingStage::UsingHexBuffer => {
                self.increment_hex_buffer()?;
            }
        }

        Ok(())
    }

    /// Read counter value as hexadecimal string
    ///
    /// # Returns
    /// Uppercase hex string (e.g., "0", "FF", "10A3")
    ///
    /// # Example
    /// ```
    /// let counter = HybridCounter::new();
    /// assert_eq!(counter.read_hex()?, "0");
    /// ```
    pub fn read_hex(&self) -> Result<String> {
        match self.current_stage {
            CountingStage::UsingU8 => Ok(format!("{:X}", self.counter_u8.unwrap())),
            CountingStage::UsingU16 => Ok(format!("{:X}", self.counter_u16.unwrap())),
            CountingStage::UsingU32 => Ok(format!("{:X}", self.counter_u32.unwrap())),
            CountingStage::UsingU64 => Ok(format!("{:X}", self.counter_u64.unwrap())),
            CountingStage::UsingHexBuffer => {
                let start_index = HEX_BUFFER_CAPACITY - self.hex_digit_count;
                let valid_slice = &self.hex_buffer[start_index..];
                String::from_utf8(valid_slice.to_vec()).map_err(|utf8_error| {
                    Error::new(
                        ErrorKind::InvalidData,
                        format!("Buffer contains invalid UTF-8: {}", utf8_error),
                    )
                })
            }
        }
    }

    /// Read counter value as decimal string (human-readable)
    ///
    /// # Algorithm
    /// For native integers: direct conversion using Display trait
    /// For hex buffer: manual conversion using repeated division
    ///
    /// # Returns
    /// Decimal string (e.g., "0", "255", "1000")
    ///
    /// # Example
    /// ```
    /// let counter = HybridCounter::new();
    /// assert_eq!(counter.read_decimal()?, "0");
    /// ```
    pub fn read_decimal(&self) -> Result<String> {
        match self.current_stage {
            CountingStage::UsingU8 => Ok(format!("{}", self.counter_u8.unwrap())),
            CountingStage::UsingU16 => Ok(format!("{}", self.counter_u16.unwrap())),
            CountingStage::UsingU32 => Ok(format!("{}", self.counter_u32.unwrap())),
            CountingStage::UsingU64 => Ok(format!("{}", self.counter_u64.unwrap())),
            CountingStage::UsingHexBuffer => {
                // Convert hex buffer to decimal string
                self.convert_hex_buffer_to_decimal()
            }
        }
    }

    /// Convert hex buffer to decimal string
    ///
    /// # Algorithm
    /// Uses repeated division by 10 (similar to how you convert any base)
    ///
    /// 1. Start with hex digits representing the number
    /// 2. Repeatedly divide by 10, collecting remainders
    /// 3. Remainders (in reverse) form the decimal representation
    ///
    /// # Performance
    /// O(n²) where n is number of digits
    /// But only called on read, not on every increment
    fn convert_hex_buffer_to_decimal(&self) -> Result<String> {
        // Get current hex value as a working copy
        let start_index = HEX_BUFFER_CAPACITY - self.hex_digit_count;
        let hex_slice = &self.hex_buffer[start_index..];

        // Convert hex ASCII to numeric values
        let mut working_digits: Vec<u8> = Vec::new();
        for &hex_char in hex_slice {
            let numeric_value = match hex_char {
                b'0'..=b'9' => hex_char - b'0',
                b'A'..=b'F' => hex_char - b'A' + 10,
                b'a'..=b'f' => hex_char - b'a' + 10,
                _ => {
                    return Err(Error::new(
                        ErrorKind::InvalidData,
                        format!("Invalid hex character: {}", hex_char),
                    ));
                }
            };
            working_digits.push(numeric_value);
        }

        // Collect decimal digits by repeated division
        let mut decimal_digits: Vec<u8> = Vec::new();

        // Continue until all digits are zero
        while !working_digits.is_empty() && !working_digits.iter().all(|&d| d == 0) {
            // Divide entire number by 10, collect remainder
            let remainder = self.divide_by_10_in_place(&mut working_digits);
            decimal_digits.push(remainder);

            // Remove leading zeros
            while !working_digits.is_empty() && working_digits[0] == 0 {
                working_digits.remove(0);
            }
        }

        // Handle zero case
        if decimal_digits.is_empty() {
            decimal_digits.push(0);
        }

        // Reverse (we collected least significant first)
        decimal_digits.reverse();

        // Convert to ASCII string
        let decimal_string: String = decimal_digits.iter().map(|&d| (b'0' + d) as char).collect();

        Ok(decimal_string)
    }

    /// Divide a multi-digit hex number by 10 in place
    ///
    /// # Arguments
    /// * `digits` - Hex digits in base-16 (each 0-15)
    ///
    /// # Returns
    /// The remainder after division
    ///
    /// # Example
    /// Input:  [1, 5, 10] (hex 15A = decimal 346)
    /// Output: 6 (remainder), digits become [0, 3, 4] (hex 34 = decimal 52)
    /// Check:  346 ÷ 10 = 34 remainder 6 ✓
    fn divide_by_10_in_place(&self, digits: &mut Vec<u8>) -> u8 {
        let mut carry = 0u16;

        for digit in digits.iter_mut() {
            // Each digit is 0-15 (hex)
            let current_value = carry * 16 + (*digit as u16);
            let quotient = current_value / 10;
            let remainder = current_value % 10;

            *digit = quotient as u8;
            carry = remainder;
        }

        carry as u8
    }

    /// Reset counter to zero
    pub fn reset(&mut self) -> Result<()> {
        self.current_stage = CountingStage::UsingU8;
        self.counter_u8 = Some(0);
        self.counter_u16 = None;
        self.counter_u32 = None;
        self.counter_u64 = None;
        self.hex_buffer = [0u8; HEX_BUFFER_CAPACITY];
        self.hex_buffer[HEX_BUFFER_CAPACITY - 1] = b'0';
        self.hex_digit_count = 1;
        Ok(())
    }

    /// Get comprehensive statistics
    ///
    /// # Returns
    /// (stage_name, value_hex, value_decimal, memory_used_bytes)
    pub fn get_statistics(&self) -> Result<(String, String, String, usize)> {
        let stage_name = self.current_stage.name().to_string();
        let value_hex = self.read_hex()?;
        let value_decimal = self.read_decimal()?;

        let memory_used = match self.current_stage {
            CountingStage::UsingU8 => 1,
            CountingStage::UsingU16 => 2,
            CountingStage::UsingU32 => 4,
            CountingStage::UsingU64 => 8,
            CountingStage::UsingHexBuffer => self.hex_digit_count,
        };

        Ok((stage_name, value_hex, value_decimal, memory_used))
    }

    /// Print detailed status report
    pub fn print_status_report(&self) -> Result<()> {
        let (stage_name, value_hex, value_decimal, memory_used) = self.get_statistics()?;

        println!("  ╔══════════════════════════════════════════════════════════╗");
        println!("  ║ Counter Status Report                                    ║");
        println!("  ╚══════════════════════════════════════════════════════════╝");
        println!("    Current stage: {}", stage_name);
        println!(
            "    Maximum for stage: {}",
            self.current_stage.max_value_description()
        );
        println!("    Value (hex): 0x{}", value_hex);
        println!("    Value (decimal): {}", value_decimal);
        println!("    Memory used: {} bytes", memory_used);
        println!(
            "    Total stack allocation: {} bytes",
            std::mem::size_of::<HybridCounter>()
        );

        Ok(())
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_creation_and_initial_state() {
        let counter = HybridCounter::new();
        assert_eq!(counter.read_decimal().unwrap(), "0");
        assert_eq!(counter.read_hex().unwrap(), "0");
        assert_eq!(counter.current_stage, CountingStage::UsingU8);
    }

    #[test]
    fn test_u8_stage_basic_counting() {
        let mut counter = HybridCounter::new();

        for i in 0..=255 {
            assert_eq!(counter.read_decimal().unwrap(), i.to_string());
            if i < 255 {
                counter.increment().unwrap();
            }
        }

        assert_eq!(counter.current_stage, CountingStage::UsingU8);
    }

    #[test]
    fn test_u8_to_u16_promotion() {
        let mut counter = HybridCounter::new();

        // Count to 255 (still u8)
        for _ in 0..255 {
            counter.increment().unwrap();
        }
        assert_eq!(counter.current_stage, CountingStage::UsingU8);
        assert_eq!(counter.read_decimal().unwrap(), "255");

        // One more increment should promote to u16
        counter.increment().unwrap();
        assert_eq!(counter.current_stage, CountingStage::UsingU16);
        assert_eq!(counter.read_decimal().unwrap(), "256");
    }

    #[test]
    fn test_u16_to_u32_promotion() {
        let mut counter = HybridCounter::new();

        // Jump to u16::MAX
        counter.counter_u8 = None;
        counter.counter_u16 = Some(u16::MAX);
        counter.current_stage = CountingStage::UsingU16;

        assert_eq!(counter.read_decimal().unwrap(), "65535");

        // Increment should promote to u32
        counter.increment().unwrap();
        assert_eq!(counter.current_stage, CountingStage::UsingU32);
        assert_eq!(counter.read_decimal().unwrap(), "65536");
    }

    #[test]
    fn test_hex_and_decimal_consistency() {
        let mut counter = HybridCounter::new();

        // Test several values
        let test_values = [0, 1, 10, 15, 16, 100, 255, 256];

        for &expected in &test_values {
            // Set counter to value
            counter.reset().unwrap();
            for _ in 0..expected {
                counter.increment().unwrap();
            }

            let decimal = counter.read_decimal().unwrap();
            let hex = counter.read_hex().unwrap();

            // Verify decimal is correct
            assert_eq!(decimal, expected.to_string());

            // Verify hex is correct
            assert_eq!(hex, format!("{:X}", expected));
        }
    }

    #[test]
    fn test_reset_functionality() {
        let mut counter = HybridCounter::new();

        // Count to some value
        for _ in 0..1000 {
            counter.increment().unwrap();
        }

        assert_ne!(counter.read_decimal().unwrap(), "0");

        // Reset
        counter.reset().unwrap();

        // Should be back to zero in u8 stage
        assert_eq!(counter.read_decimal().unwrap(), "0");
        assert_eq!(counter.current_stage, CountingStage::UsingU8);
    }

    #[test]
    fn test_large_number_hex_to_decimal() {
        let mut counter = HybridCounter::new();

        // Set to a known large value (1000 decimal = 0x3E8 hex)
        for _ in 0..1000 {
            counter.increment().unwrap();
        }

        assert_eq!(counter.read_hex().unwrap(), "3E8");
        assert_eq!(counter.read_decimal().unwrap(), "1000");
    }
}

/// Demonstration main function
fn main() -> Result<()> {
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║  Hybrid Counter: Native Integers First, Hex Buffer Fallback ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    let mut counter = HybridCounter::new();

    println!("Initial state:");
    counter.print_status_report()?;

    // Test u8 stage
    println!("\n\nCounting in u8 stage...");
    for _ in 0..250 {
        counter.increment()?;
    }
    counter.print_status_report()?;

    // Cross u8→u16 boundary
    println!("\n\nCrossing u8→u16 boundary...");
    for _ in 0..10 {
        counter.increment()?;
    }
    counter.print_status_report()?;

    // Count to a recognizable number
    println!("\n\nCounting to 1000...");
    counter.reset()?;
    for _ in 0..1000 {
        counter.increment()?;
    }
    counter.print_status_report()?;

    // Count to realistic file count (180,000)
    println!("\n\nCounting to 180,000 (realistic large file count)...");
    counter.reset()?;
    for _ in 0..180000 {
        counter.increment()?;
    }
    counter.print_status_report()?;

    println!("\n\n╔══════════════════════════════════════════════════════════════╗");
    println!("║  Key Insights                                                ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!("  • 180,000 files fits in u32 (4 bytes)");
    println!("  • Native integer performance: ~1-2 nanoseconds per increment");
    println!("  • Hex buffer only needed for counts > 18 quintillion");
    println!("  • Stage transitions are rare exception-handling events");
    println!("  • Decimal output for human readability");
    println!("  • Hex storage for space efficiency\n");

    let mut counter = HybridCounter::new();

    // Count files in directory
    for entry in std::fs::read_dir(
        "/home/oops/code/gutenberg_babble/perseids/byte_perseid/pseudo_toml_maker_training_data/toml_production_output_60000v2",
    )? {
        let _ = entry?;
        counter.increment()?;
    }

    // println!("Count: 0x{}", counter.read()?);
    counter.print_status_report()?;

    Ok(())
}
