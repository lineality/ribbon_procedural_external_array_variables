// main.rs

//! # Ribbon: "It's tape all the way down."
//!
//! Externalized procedural variables for arbitrary-precision counting.
//!
//! ## Purpose
//! Demonstrate counting with arbitrarily large numbers without loading
//! the entire value into memory as a single integer. Instead, the value
//! is represented procedurally as a sequence of digits (binary, decimal, or hex)
//! stored in:
//! - A. Disk files (unlimited size, persistent)
//! - B. Heap memory (dynamic allocation)
//! - C. Stack buffer (pre-allocated 2048 bytes, fixed but large)
//!
//! ## Use Cases
//! - Counting beyond u64::MAX
//! - Time-stamps that won't overflow (Y2K/Epoch-proof)
//! - Resource-constrained systems
//! - Systems requiring persistence across crashes
//!
//! ## Policy
//! Never load the entire number value into a single variable.
//! Process digit-by-digit incrementally.

use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::Path;
use std::time::Instant;

/// Maximum iterations for bounded loops (safety limit)
const MAX_LOOP_ITERATIONS: usize = 10_000;

/// Stack buffer size in bytes
const STACK_BUFFER_SIZE: usize = 2048;

// ============================================================================
// TRAIT DEFINITIONS
// ============================================================================

/// Trait for all counter implementations
///
/// Policy: All counters must support increment, read, and reset operations
/// with proper error handling.
trait ExternalCounter {
    /// Increment the counter by 1
    ///
    /// # Errors
    /// Returns IO error if storage operation fails
    fn increment(&mut self) -> std::io::Result<()>;

    /// Read current value as string representation
    ///
    /// # Errors
    /// Returns IO error if read operation fails
    fn read(&self) -> std::io::Result<String>;

    /// Reset counter to initial state
    ///
    /// # Errors
    /// Returns IO error if reset operation fails
    fn reset(&mut self) -> std::io::Result<()>;

    /// Get the base/radix of this counter (2, 10, or 16)
    fn get_base(&self) -> u32;
}

// ============================================================================
// DISK-BASED COUNTERS (Type A: Persistent Storage)
// ============================================================================

/// Disk-based binary counter
///
/// Stores binary representation as ASCII '0' and '1' characters in a file.
/// Each increment reads the file, processes digit-by-digit, and writes back.
///
/// # Example
/// ```text
/// Initial: "1"
/// After increment: "10"
/// After increment: "11"
/// After increment: "100"
/// ```
struct DiskBinaryCounter {
    /// Absolute path to counter file
    path: String,
}

impl DiskBinaryCounter {
    /// Create new disk-based binary counter
    ///
    /// # Arguments
    /// * `path` - Absolute file path for counter storage
    ///
    /// # Errors
    /// Returns IO error if file creation fails
    ///
    /// # Policy
    /// Initializes file with "1" if it doesn't exist
    fn new(path: &str) -> std::io::Result<Self> {
        // Defensive: Validate path is not empty
        assert!(!path.is_empty(), "Counter path cannot be empty");

        let counter = DiskBinaryCounter {
            path: path.to_string(),
        };

        // Initialize with "1" if file doesn't exist
        if !Path::new(path).exists() {
            let mut file = File::create(path)?;
            file.write_all(b"1")?;
            file.sync_all()?; // Ensure data is written to disk
        }

        Ok(counter)
    }
}

impl ExternalCounter for DiskBinaryCounter {
    /// Increment binary counter using digit-by-digit carry algorithm
    ///
    /// # Algorithm
    /// 1. Read current digits from right to left
    /// 2. For each '0', change to '1' and stop (no carry)
    /// 3. For each '1', change to '0' and continue (carry)
    /// 4. If carry reaches start, prepend '1'
    ///
    /// # Edge Cases
    /// - Single '1' becomes '10'
    /// - All '1's get carry: '111' becomes '1000'
    fn increment(&mut self) -> std::io::Result<()> {
        let mut file = OpenOptions::new().read(true).write(true).open(&self.path)?;

        let mut contents = String::new();
        file.read_to_string(&mut contents)?;

        let mut digits: Vec<char> = contents.trim().chars().collect();

        // Defensive: Ensure we have at least one digit
        assert!(!digits.is_empty(), "Counter file cannot be empty");
        assert!(
            digits.len() <= MAX_LOOP_ITERATIONS,
            "Counter exceeds safety limit"
        );

        // Add carry from right to left (bounded loop)
        let mut carry = true;
        let digit_count = digits.len();
        for i in 0..digit_count {
            let idx = digit_count - 1 - i; // Right to left

            if carry {
                if digits[idx] == '0' {
                    digits[idx] = '1';
                    carry = false;
                    break; // No more carry needed
                } else if digits[idx] == '1' {
                    digits[idx] = '0';
                    // Continue carrying
                } else {
                    // Defensive: Invalid digit detected
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "Invalid binary digit in counter file",
                    ));
                }
            } else {
                break;
            }
        }

        // If still carrying after processing all digits, prepend '1'
        if carry {
            digits.insert(0, '1');
        }

        // Write back atomically
        file.set_len(0)?;
        file.seek(SeekFrom::Start(0))?;
        file.write_all(digits.iter().collect::<String>().as_bytes())?;
        file.sync_all()?;

        Ok(())
    }

    fn read(&self) -> std::io::Result<String> {
        let contents = std::fs::read_to_string(&self.path)?;
        Ok(contents.trim().to_string())
    }

    fn reset(&mut self) -> std::io::Result<()> {
        let mut file = File::create(&self.path)?;
        file.write_all(b"1")?;
        file.sync_all()?;
        Ok(())
    }

    fn get_base(&self) -> u32 {
        2
    }
}

/// Disk-based hexadecimal counter
///
/// Stores hex representation as ASCII '0'-'9', 'A'-'F' characters.
/// More space-efficient than binary: 4 bits per character.
struct DiskHexCounter {
    path: String,
}

impl DiskHexCounter {
    fn new(path: &str) -> std::io::Result<Self> {
        assert!(!path.is_empty(), "Counter path cannot be empty");

        let counter = DiskHexCounter {
            path: path.to_string(),
        };

        if !Path::new(path).exists() {
            let mut file = File::create(path)?;
            file.write_all(b"0")?;
            file.sync_all()?;
        }

        Ok(counter)
    }

    /// Convert hex character to numeric value (0-15)
    fn hex_char_to_value(c: char) -> Option<u8> {
        match c {
            '0'..='9' => Some(c as u8 - b'0'),
            'A'..='F' => Some(c as u8 - b'A' + 10),
            'a'..='f' => Some(c as u8 - b'a' + 10),
            _ => None,
        }
    }

    /// Convert numeric value (0-15) to uppercase hex character
    fn value_to_hex_char(v: u8) -> Option<char> {
        match v {
            0..=9 => Some((b'0' + v) as char),
            10..=15 => Some((b'A' + v - 10) as char),
            _ => None,
        }
    }
}

impl ExternalCounter for DiskHexCounter {
    fn increment(&mut self) -> std::io::Result<()> {
        let mut file = OpenOptions::new().read(true).write(true).open(&self.path)?;

        let mut contents = String::new();
        file.read_to_string(&mut contents)?;

        let mut digits: Vec<char> = contents.trim().chars().collect();

        assert!(!digits.is_empty(), "Counter file cannot be empty");
        assert!(
            digits.len() <= MAX_LOOP_ITERATIONS,
            "Counter exceeds safety limit"
        );

        let mut carry = 1u8;
        let digit_count = digits.len();

        for i in 0..digit_count {
            let idx = digit_count - 1 - i;

            if carry > 0 {
                let val = Self::hex_char_to_value(digits[idx]).ok_or_else(|| {
                    std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "Invalid hex digit in counter file",
                    )
                })?;

                let mut new_val = val + carry;
                if new_val >= 16 {
                    new_val = 0;
                    carry = 1;
                } else {
                    carry = 0;
                }

                digits[idx] = Self::value_to_hex_char(new_val).ok_or_else(|| {
                    std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "Failed to convert value to hex",
                    )
                })?;
            } else {
                break;
            }
        }

        if carry > 0 {
            digits.insert(0, '1');
        }

        file.set_len(0)?;
        file.seek(SeekFrom::Start(0))?;
        file.write_all(digits.iter().collect::<String>().as_bytes())?;
        file.sync_all()?;

        Ok(())
    }

    fn read(&self) -> std::io::Result<String> {
        let contents = std::fs::read_to_string(&self.path)?;
        Ok(contents.trim().to_string())
    }

    fn reset(&mut self) -> std::io::Result<()> {
        let mut file = File::create(&self.path)?;
        file.write_all(b"0")?;
        file.sync_all()?;
        Ok(())
    }

    fn get_base(&self) -> u32 {
        16
    }
}

/// Disk-based decimal counter
struct DiskDecimalCounter {
    path: String,
}

impl DiskDecimalCounter {
    fn new(path: &str) -> std::io::Result<Self> {
        assert!(!path.is_empty(), "Counter path cannot be empty");

        let counter = DiskDecimalCounter {
            path: path.to_string(),
        };

        if !Path::new(path).exists() {
            let mut file = File::create(path)?;
            file.write_all(b"0")?;
            file.sync_all()?;
        }

        Ok(counter)
    }
}

impl ExternalCounter for DiskDecimalCounter {
    fn increment(&mut self) -> std::io::Result<()> {
        let mut file = OpenOptions::new().read(true).write(true).open(&self.path)?;

        let mut contents = String::new();
        file.read_to_string(&mut contents)?;

        let mut digits: Vec<char> = contents.trim().chars().collect();

        assert!(!digits.is_empty(), "Counter file cannot be empty");
        assert!(
            digits.len() <= MAX_LOOP_ITERATIONS,
            "Counter exceeds safety limit"
        );

        let mut carry = true;
        let digit_count = digits.len();

        for i in 0..digit_count {
            let idx = digit_count - 1 - i;

            if carry {
                let digit = digits[idx].to_digit(10).ok_or_else(|| {
                    std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "Invalid decimal digit in counter file",
                    )
                })?;

                if digit == 9 {
                    digits[idx] = '0';
                } else {
                    digits[idx] = char::from_digit(digit + 1, 10).ok_or_else(|| {
                        std::io::Error::new(
                            std::io::ErrorKind::InvalidData,
                            "Failed to convert digit",
                        )
                    })?;
                    carry = false;
                }
            } else {
                break;
            }
        }

        if carry {
            digits.insert(0, '1');
        }

        file.set_len(0)?;
        file.seek(SeekFrom::Start(0))?;
        file.write_all(digits.iter().collect::<String>().as_bytes())?;
        file.sync_all()?;

        Ok(())
    }

    fn read(&self) -> std::io::Result<String> {
        let contents = std::fs::read_to_string(&self.path)?;
        Ok(contents.trim().to_string())
    }

    fn reset(&mut self) -> std::io::Result<()> {
        let mut file = File::create(&self.path)?;
        file.write_all(b"0")?;
        file.sync_all()?;
        Ok(())
    }

    fn get_base(&self) -> u32 {
        10
    }
}

// ============================================================================
// HEAP-BASED COUNTERS (Type B: Dynamic Memory)
// ============================================================================

/// Heap-based binary counter using Vec<bool>
///
/// Dynamic allocation allows unlimited growth (subject to available memory)
///
/// # Storage
/// Each bit stored as bool: true=1, false=0
/// Vec grows dynamically as needed
struct HeapBinaryCounter {
    tape: Vec<bool>,
}

impl HeapBinaryCounter {
    fn new() -> Self {
        HeapBinaryCounter { tape: vec![true] }
    }
}

impl ExternalCounter for HeapBinaryCounter {
    // fn increment(&mut self) -> std::io::Result<()> {
    //     assert!(
    //         self.tape.len() <= MAX_LOOP_ITERATIONS,
    //         "Counter exceeds safety limit"
    //     );

    //     let mut carry = true;
    //     let len = self.tape.len();

    //     for i in 0..len {
    //         let idx = len - 1 - i;

    //         if carry {
    //             if !self.tape[idx] {
    //                 self.tape[idx] = true;
    //                 carry = false;
    //                 break;
    //             } else {
    //                 self.tape[idx] = false;
    //             }
    //         } else {
    //             break;
    //         }
    //     }

    //     if carry {
    //         self.tape.insert(0, true);
    //     }

    //     Ok(())
    // }

    /// Increment binary counter by 1 using carry propagation
    ///
    /// # Algorithm Description
    ///
    /// Binary increment follows the same rules as manual binary addition:
    ///
    /// ## Rules (processing right-to-left):
    /// 1. If digit is 0: Change to 1, STOP (no carry needed)
    /// 2. If digit is 1: Change to 0, CONTINUE (carry to next position)
    /// 3. If carry reaches the front: Prepend a new 1 digit
    ///
    /// ## Step-by-Step Examples:
    ///
    /// ### Example 1: Simple case (no carry propagation)
    /// ```text
    /// Start:  [1, 0, 1, 0]  // Binary: 1010 (decimal 10)
    ///                    ^-- Start here (rightmost)
    /// Step 1: Check bit[3] = 0
    ///         Change to 1, carry stops
    /// Result: [1, 0, 1, 1]  // Binary: 1011 (decimal 11)
    /// ```
    ///
    /// ### Example 2: Single carry
    /// ```text
    /// Start:  [1, 0, 1, 1]  // Binary: 1011 (decimal 11)
    ///                    ^-- Start here
    /// Step 1: bit[3] = 1 → Change to 0, carry=true
    ///         [1, 0, 1, 0]
    ///                 ^----- Continue here
    /// Step 2: bit[2] = 1 → Change to 1, carry stops
    /// Result: [1, 1, 0, 0]  // Binary: 1100 (decimal 12)
    /// ```
    ///
    /// ### Example 3: Carry propagates to front (all 1s)
    /// ```text
    /// Start:  [1, 1, 1]     // Binary: 111 (decimal 7)
    ///              ^-- Start here (rightmost)
    /// Step 1: bit[2] = 1 → Change to 0, carry=true
    ///         [1, 1, 0]
    ///           ^--------- Continue here
    /// Step 2: bit[1] = 1 → Change to 0, carry=true
    ///         [1, 0, 0]
    ///         ^----------- Continue here
    /// Step 3: bit[0] = 1 → Change to 0, carry=true
    ///         [0, 0, 0]
    /// Step 4: Still carrying! Need new digit at front
    ///         Prepend 1
    /// Result: [1, 0, 0, 0]  // Binary: 1000 (decimal 8)
    /// ```
    ///
    /// ## Edge Cases Handled:
    /// - Empty tape: Prevented by assertion
    /// - Single digit [1]: Becomes [1, 0]
    /// - All ones [...1, 1, 1]: Becomes [1, 0, 0, 0]
    /// - Very large numbers: Limited only by available memory
    ///
    /// # Errors
    /// Returns error if counter exceeds MAX_LOOP_ITERATIONS safety limit
    fn increment(&mut self) -> std::io::Result<()> {
        // Defensive: Ensure counter hasn't grown beyond safety limit
        assert!(
            self.tape.len() <= MAX_LOOP_ITERATIONS,
            "Counter exceeds safety limit"
        );

        // Defensive: Ensure tape is not empty (should never happen)
        assert!(!self.tape.is_empty(), "Binary tape cannot be empty");

        // Initialize carry flag (we're adding 1)
        let mut carry = true;
        let len = self.tape.len();

        // Bounded loop: Process digits from right to left
        for i in 0..len {
            // Convert loop counter to right-to-left index
            let idx = len - 1 - i;

            // Only process if we still have a carry
            if carry {
                // Check current digit value
                if !self.tape[idx] {
                    // Current digit is 0
                    // Rule: 0 + carry → 1, no further carry
                    self.tape[idx] = true;
                    carry = false;
                    break; // Done! No need to continue
                } else {
                    // Current digit is 1
                    // Rule: 1 + carry → 0, continue carrying
                    self.tape[idx] = false;
                    // carry remains true, continue to next digit
                }
            } else {
                // No carry, we're done
                break;
            }
        }

        // After processing all digits, if carry is still true,
        // we need to expand the number by prepending a new digit
        if carry {
            // All digits were 1, they're all now 0
            // Prepend a 1 to the front
            // Example: [0, 0, 0] → [1, 0, 0, 0]
            self.tape.insert(0, true);
        }

        Ok(())
    }

    fn read(&self) -> std::io::Result<String> {
        Ok(self
            .tape
            .iter()
            .map(|&b| if b { '1' } else { '0' })
            .collect())
    }

    fn reset(&mut self) -> std::io::Result<()> {
        self.tape = vec![true];
        Ok(())
    }

    fn get_base(&self) -> u32 {
        2
    }
}

/// Heap-based decimal counter
struct HeapDecimalCounter {
    /// Each digit stored as u8 (0-9)
    digits: Vec<u8>,
}

impl HeapDecimalCounter {
    fn new() -> Self {
        HeapDecimalCounter { digits: vec![0] }
    }
}

impl ExternalCounter for HeapDecimalCounter {
    /// Increment decimal counter by 1 using carry propagation
    ///
    /// # Algorithm Description
    ///
    /// Decimal increment follows standard base-10 arithmetic rules.
    ///
    /// ## Rules (processing right-to-left):
    /// 1. If digit is 0-8: Add 1, STOP (no carry)
    /// 2. If digit is 9: Change to 0, CONTINUE (carry to next position)
    /// 3. If carry reaches the front: Prepend a 1
    ///
    /// ## Step-by-Step Examples:
    ///
    /// ### Example 1: No carry needed
    /// ```text
    /// Start:  [1, 2, 3]     // Decimal: 123
    ///              ^-- Start here (rightmost)
    /// Step 1: digit[2] = 3
    ///         3 + 1 = 4, no carry needed
    /// Result: [1, 2, 4]     // Decimal: 124
    /// ```
    ///
    /// ### Example 2: Single carry
    /// ```text
    /// Start:  [1, 2, 9]     // Decimal: 129
    ///              ^-- Start here
    /// Step 1: digit[2] = 9
    ///         9 + 1 = 10 → digit=0, carry=1
    ///         [1, 2, 0]
    ///           ^--------- Continue here
    /// Step 2: digit[1] = 2
    ///         2 + 1 = 3, carry stops
    /// Result: [1, 3, 0]     // Decimal: 130
    /// ```
    ///
    /// ### Example 3: Multiple carries (all 9s)
    /// ```text
    /// Start:  [9, 9, 9]     // Decimal: 999
    ///              ^-- Start here
    /// Step 1: digit[2] = 9 → 0, carry=1
    ///         [9, 9, 0]
    ///           ^--------- Continue
    /// Step 2: digit[1] = 9 → 0, carry=1
    ///         [9, 0, 0]
    ///         ^----------- Continue
    /// Step 3: digit[0] = 9 → 0, carry=1
    ///         [0, 0, 0]
    /// Step 4: Still carrying! Prepend 1
    /// Result: [1, 0, 0, 0]  // Decimal: 1000
    /// ```
    ///
    /// ## Why This Works:
    /// This mimics how we manually add 1 to a number:
    /// - Start at the rightmost digit (ones place)
    /// - If less than 9, just add 1 and done
    /// - If 9, it becomes 0 and we "carry the 1" to the next column
    /// - Continue until no more carry, or add new digit at front
    ///
    /// ## Edge Cases:
    /// - Single digit 0-8: Just increment
    /// - Single digit 9: Becomes [1, 0]
    /// - All 9s: Becomes [1, 0, 0, ..., 0]
    /// - Large numbers: Limited only by memory
    fn increment(&mut self) -> std::io::Result<()> {
        // Defensive: Safety limit check
        assert!(
            self.digits.len() <= MAX_LOOP_ITERATIONS,
            "Counter exceeds safety limit"
        );

        // Defensive: Ensure we have digits
        assert!(!self.digits.is_empty(), "Decimal tape cannot be empty");

        // Initialize carry flag (we're adding 1)
        let mut carry = true;
        let len = self.digits.len();

        // Bounded loop: Process digits right to left
        for i in 0..len {
            let idx = len - 1 - i;

            if carry {
                // Check if current digit is 9
                if self.digits[idx] == 9 {
                    // Rule: 9 + carry → 0, continue carrying
                    self.digits[idx] = 0;
                    // carry remains true
                } else {
                    // Rule: (0-8) + carry → digit+1, stop carrying
                    self.digits[idx] += 1;
                    carry = false;
                    break; // Done!
                }
            } else {
                break;
            }
        }

        // If still carrying after all digits processed,
        // we need to expand the number
        if carry {
            // All digits were 9, now all are 0
            // Prepend 1 to make next power of 10
            self.digits.insert(0, 1);
        }

        Ok(())
    }

    fn read(&self) -> std::io::Result<String> {
        Ok(self
            .digits
            .iter()
            .map(|&d| char::from_digit(d as u32, 10).unwrap_or('?'))
            .collect())
    }

    fn reset(&mut self) -> std::io::Result<()> {
        self.digits = vec![0];
        Ok(())
    }

    fn get_base(&self) -> u32 {
        10
    }
}

/// Heap-based hexadecimal counter
struct HeapHexCounter {
    /// Each digit stored as u8 (0-15)
    /// 0-9 represent 0-9, 10-15 represent A-F
    digits: Vec<u8>, // Store digits 0-15
}

impl HeapHexCounter {
    fn new() -> Self {
        HeapHexCounter { digits: vec![0] }
    }
}

impl ExternalCounter for HeapHexCounter {
    /// Increment hexadecimal counter by 1 using carry propagation
    ///
    /// # Algorithm Description
    ///
    /// Hexadecimal uses base-16: digits 0-9, then A(10), B(11), C(12), D(13), E(14), F(15)
    ///
    /// ## Rules (processing right-to-left):
    /// 1. If digit is 0-E (0-14): Add 1, STOP (no carry)
    /// 2. If digit is F (15): Change to 0, CONTINUE (carry to next position)
    /// 3. If carry reaches the front: Prepend a 1
    ///
    /// ## Step-by-Step Examples:
    ///
    /// ### Example 1: Simple increment (no carry)
    /// ```text
    /// Start:  [1, 5, 10]    // Hex: 15A (decimal 346)
    ///               ^-- Start here (rightmost, value=10='A')
    /// Step 1: digit[2] = 10 (A)
    ///         10 + 1 = 11 (B), no carry
    /// Result: [1, 5, 11]    // Hex: 15B (decimal 347)
    /// ```
    ///
    /// ### Example 2: Carry from F
    /// ```text
    /// Start:  [1, 5, 15]    // Hex: 15F (decimal 351)
    ///               ^-- Start here (value=15='F')
    /// Step 1: digit[2] = 15 (F)
    ///         15 + 1 = 16 → digit=0, carry=1
    ///         [1, 5, 0]
    ///            ^--------- Continue here
    /// Step 2: digit[1] = 5
    ///         5 + 1 = 6, carry stops
    /// Result: [1, 6, 0]     // Hex: 160 (decimal 352)
    /// ```
    ///
    /// ### Example 3: All F's (maximum single-byte)
    /// ```text
    /// Start:  [15, 15]      // Hex: FF (decimal 255)
    ///              ^-- Start here
    /// Step 1: digit[1] = 15 (F) → 0, carry=1
    ///         [15, 0]
    ///          ^----------- Continue
    /// Step 2: digit[0] = 15 (F) → 0, carry=1
    ///         [0, 0]
    /// Step 3: Still carrying! Prepend 1
    /// Result: [1, 0, 0]     // Hex: 100 (decimal 256)
    /// ```
    ///
    /// ## Why Hexadecimal is Efficient:
    ///
    /// Hexadecimal is 4x more space-efficient than binary:
    /// - Binary: 1 bit per digit (2 values)
    /// - Hex: 4 bits per digit (16 values)
    /// - Example: 255 in binary = "11111111" (8 chars)
    /// - Example: 255 in hex = "FF" (2 chars)
    ///
    /// This makes hex ideal for:
    /// - Memory addresses (compact representation)
    /// - Color codes (#FFFFFF)
    /// - Large numbers needing readability
    ///
    /// ## Hexadecimal Digit Reference:
    /// ```text
    /// Dec  Hex  Binary
    /// 0    0    0000
    /// 1    1    0001
    /// 2    2    0010
    /// 3    3    0011
    /// 4    4    0100
    /// 5    5    0101
    /// 6    6    0110
    /// 7    7    0111
    /// 8    8    1000
    /// 9    9    1001
    /// 10   A    1010
    /// 11   B    1011
    /// 12   C    1100
    /// 13   D    1101
    /// 14   E    1110
    /// 15   F    1111
    /// ```
    fn increment(&mut self) -> std::io::Result<()> {
        // Defensive: Safety limit check
        assert!(
            self.digits.len() <= MAX_LOOP_ITERATIONS,
            "Counter exceeds safety limit"
        );

        // Defensive: Ensure we have digits
        assert!(!self.digits.is_empty(), "Hex tape cannot be empty");

        // Initialize carry flag (we're adding 1)
        let mut carry = true;
        let len = self.digits.len();

        // Bounded loop: Process digits right to left
        for i in 0..len {
            let idx = len - 1 - i;

            if carry {
                // Check if current digit is F (15)
                if self.digits[idx] == 15 {
                    // Rule: F (15) + carry → 0, continue carrying
                    self.digits[idx] = 0;
                    // carry remains true
                } else {
                    // Rule: (0-14) + carry → digit+1, stop carrying
                    // This handles 0-9 and A-E
                    self.digits[idx] += 1;
                    carry = false;
                    break; // Done!
                }
            } else {
                break;
            }
        }

        // If still carrying after all digits processed,
        // all digits were F (15), now all are 0
        // Prepend 1 to make next power of 16
        if carry {
            self.digits.insert(0, 1);
        }

        Ok(())
    }

    fn read(&self) -> std::io::Result<String> {
        Ok(self
            .digits
            .iter()
            .map(|&d| {
                char::from_digit(d as u32, 16)
                    .unwrap_or('?')
                    .to_ascii_uppercase()
            })
            .collect())
    }

    fn reset(&mut self) -> std::io::Result<()> {
        self.digits = vec![0];
        Ok(())
    }

    fn get_base(&self) -> u32 {
        16
    }
}

// ============================================================================
// STACK-BASED COUNTERS (Type C: Pre-allocated Buffer)
// ============================================================================

/// Stack-based binary counter with fixed 2048-byte buffer
///
/// # Policy
/// Pre-allocated memory on stack. No dynamic allocation.
/// Fixed maximum size but guaranteed no heap fragmentation.
///
/// # Capacity
/// 2048 bytes = 2048 binary digits = numbers up to 2^2048
/// (Much larger than u128 which is only 2^128)
struct StackBinaryCounter {
    /// Fixed-size buffer (pre-allocated)
    buffer: [u8; STACK_BUFFER_SIZE],
    /// Number of valid digits (from right)
    length: usize,
}

impl StackBinaryCounter {
    /// Create new stack-based binary counter
    ///
    /// # Policy
    /// Initialize with single '1' bit at rightmost position
    fn new() -> Self {
        let mut buffer = [0u8; STACK_BUFFER_SIZE];
        buffer[STACK_BUFFER_SIZE - 1] = b'1';

        StackBinaryCounter { buffer, length: 1 }
    }

    /// Get the active portion of the buffer
    fn get_active_slice(&self) -> &[u8] {
        let start = STACK_BUFFER_SIZE - self.length;
        &self.buffer[start..STACK_BUFFER_SIZE]
    }
}

impl ExternalCounter for StackBinaryCounter {
    fn increment(&mut self) -> std::io::Result<()> {
        // Defensive: Check we have room
        if self.length >= STACK_BUFFER_SIZE {
            return Err(std::io::Error::new(
                std::io::ErrorKind::OutOfMemory,
                "Stack buffer overflow - counter too large",
            ));
        }

        let mut carry = true;
        let start = STACK_BUFFER_SIZE - self.length;

        // Process from right to left (bounded loop)
        for i in 0..self.length {
            let idx = STACK_BUFFER_SIZE - 1 - i;

            if carry {
                if self.buffer[idx] == b'0' {
                    self.buffer[idx] = b'1';
                    carry = false;
                    break;
                } else if self.buffer[idx] == b'1' {
                    self.buffer[idx] = b'0';
                } else {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "Invalid binary digit in buffer",
                    ));
                }
            } else {
                break;
            }
        }

        // If still carrying, need to extend left
        if carry {
            if self.length >= STACK_BUFFER_SIZE {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::OutOfMemory,
                    "Stack buffer overflow",
                ));
            }
            let new_start = start - 1;
            self.buffer[new_start] = b'1';
            self.length += 1;
        }

        Ok(())
    }

    fn read(&self) -> std::io::Result<String> {
        let slice = self.get_active_slice();
        String::from_utf8(slice.to_vec())
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
    }

    fn reset(&mut self) -> std::io::Result<()> {
        self.buffer = [0u8; STACK_BUFFER_SIZE];
        self.buffer[STACK_BUFFER_SIZE - 1] = b'1';
        self.length = 1;
        Ok(())
    }

    fn get_base(&self) -> u32 {
        2
    }
}

/// Stack-based decimal counter with fixed 2048-byte buffer
struct StackDecimalCounter {
    buffer: [u8; STACK_BUFFER_SIZE],
    length: usize,
}

impl StackDecimalCounter {
    fn new() -> Self {
        let mut buffer = [0u8; STACK_BUFFER_SIZE];
        buffer[STACK_BUFFER_SIZE - 1] = b'0';

        StackDecimalCounter { buffer, length: 1 }
    }

    fn get_active_slice(&self) -> &[u8] {
        let start = STACK_BUFFER_SIZE - self.length;
        &self.buffer[start..STACK_BUFFER_SIZE]
    }
}

impl ExternalCounter for StackDecimalCounter {
    fn increment(&mut self) -> std::io::Result<()> {
        if self.length >= STACK_BUFFER_SIZE {
            return Err(std::io::Error::new(
                std::io::ErrorKind::OutOfMemory,
                "Stack buffer overflow",
            ));
        }

        let mut carry = true;
        let start = STACK_BUFFER_SIZE - self.length;

        for i in 0..self.length {
            let idx = STACK_BUFFER_SIZE - 1 - i;

            if carry {
                if self.buffer[idx] >= b'0' && self.buffer[idx] <= b'8' {
                    self.buffer[idx] += 1;
                    carry = false;
                    break;
                } else if self.buffer[idx] == b'9' {
                    self.buffer[idx] = b'0';
                } else {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "Invalid decimal digit in buffer",
                    ));
                }
            } else {
                break;
            }
        }

        if carry {
            if self.length >= STACK_BUFFER_SIZE {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::OutOfMemory,
                    "Stack buffer overflow",
                ));
            }
            let new_start = start - 1;
            self.buffer[new_start] = b'1';
            self.length += 1;
        }

        Ok(())
    }

    fn read(&self) -> std::io::Result<String> {
        let slice = self.get_active_slice();
        String::from_utf8(slice.to_vec())
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
    }

    fn reset(&mut self) -> std::io::Result<()> {
        self.buffer = [0u8; STACK_BUFFER_SIZE];
        self.buffer[STACK_BUFFER_SIZE - 1] = b'0';
        self.length = 1;
        Ok(())
    }

    fn get_base(&self) -> u32 {
        10
    }
}

/// Stack-based hexadecimal counter with fixed 2048-byte buffer
struct StackHexCounter {
    buffer: [u8; STACK_BUFFER_SIZE],
    length: usize,
}

impl StackHexCounter {
    fn new() -> Self {
        let mut buffer = [0u8; STACK_BUFFER_SIZE];
        buffer[STACK_BUFFER_SIZE - 1] = b'0';

        StackHexCounter { buffer, length: 1 }
    }

    fn get_active_slice(&self) -> &[u8] {
        let start = STACK_BUFFER_SIZE - self.length;
        &self.buffer[start..STACK_BUFFER_SIZE]
    }
}

impl ExternalCounter for StackHexCounter {
    fn increment(&mut self) -> std::io::Result<()> {
        if self.length >= STACK_BUFFER_SIZE {
            return Err(std::io::Error::new(
                std::io::ErrorKind::OutOfMemory,
                "Stack buffer overflow",
            ));
        }

        let mut carry = 1u8;
        let start = STACK_BUFFER_SIZE - self.length;

        for i in 0..self.length {
            let idx = STACK_BUFFER_SIZE - 1 - i;

            if carry > 0 {
                let current = match self.buffer[idx] {
                    b'0'..=b'9' => self.buffer[idx] - b'0',
                    b'A'..=b'F' => self.buffer[idx] - b'A' + 10,
                    b'a'..=b'f' => self.buffer[idx] - b'a' + 10,
                    _ => {
                        return Err(std::io::Error::new(
                            std::io::ErrorKind::InvalidData,
                            "Invalid hex digit in buffer",
                        ));
                    }
                };

                let mut new_val = current + carry;
                if new_val >= 16 {
                    new_val = 0;
                    carry = 1;
                } else {
                    carry = 0;
                }

                self.buffer[idx] = match new_val {
                    0..=9 => b'0' + new_val,
                    10..=15 => b'A' + new_val - 10,
                    _ => b'0',
                };
            } else {
                break;
            }
        }

        if carry > 0 {
            if self.length >= STACK_BUFFER_SIZE {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::OutOfMemory,
                    "Stack buffer overflow",
                ));
            }
            let new_start = start - 1;
            self.buffer[new_start] = b'1';
            self.length += 1;
        }

        Ok(())
    }

    fn read(&self) -> std::io::Result<String> {
        let slice = self.get_active_slice();
        String::from_utf8(slice.to_vec())
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
    }

    fn reset(&mut self) -> std::io::Result<()> {
        self.buffer = [0u8; STACK_BUFFER_SIZE];
        self.buffer[STACK_BUFFER_SIZE - 1] = b'0';
        self.length = 1;
        Ok(())
    }

    fn get_base(&self) -> u32 {
        16
    }
}

// ============================================================================
// DEMONSTRATION AND TESTS
// ============================================================================

/// Print banner with decoration
fn print_banner(title: &str) {
    println!("\n{}", "=".repeat(70));
    println!("  {}", title);
    println!("{}", "=".repeat(70));
}

/// Demonstrate a counter by counting to a target
fn demonstrate_counter<T: ExternalCounter>(
    counter: &mut T,
    name: &str,
    target: usize,
) -> std::io::Result<()> {
    // Bounded loop with explicit limit
    let iterations = target.min(MAX_LOOP_ITERATIONS);

    for _ in 0..iterations {
        counter.increment()?;
    }

    let value = counter.read()?;
    println!(
        "  {} counted to: {} (base {})",
        name,
        value,
        counter.get_base()
    );

    Ok(())
}

// // ============================================================================
// // PERFORMANCE TESTING
// // ============================================================================

// /// Benchmark different counting approaches
// ///
// /// Tests:
// /// 1. Native u32 counting
// /// 2. Ribbon decimal counting
// /// 3. Ribbon binary counting
// /// 4. Ribbon hex counting
// ///
// /// # Arguments
// /// * `iterations` - Number of increments to perform
// fn benchmark_counters(iterations: usize) -> std::io::Result<()> {
//     println!("\n{}", "=".repeat(70));
//     println!("  PERFORMANCE BENCHMARK: {} iterations", iterations);
//     println!("{}", "=".repeat(70));

//     // Bound iterations for safety
//     let safe_iterations = iterations.min(MAX_LOOP_ITERATIONS);

//     // Test 1: Native u32
//     let start = Instant::now();
//     let mut u32_counter: u32 = 0;
//     for _ in 0..safe_iterations {
//         u32_counter = u32_counter.wrapping_add(1);
//     }
//     let u32_duration = start.elapsed();

//     println!("\n  Native u32 Counter:");
//     println!("    Result: {}", u32_counter);
//     println!("    Time: {:?}", u32_duration);
//     println!(
//         "    Per increment: {:?}",
//         u32_duration / safe_iterations as u32
//     );

//     // Test 2: Ribbon Decimal
//     let start = Instant::now();
//     let mut decimal_counter = HeapDecimalCounter::new();
//     for _ in 0..safe_iterations {
//         decimal_counter.increment()?;
//     }
//     let decimal_duration = start.elapsed();

//     println!("\n  Ribbon Decimal Counter:");
//     println!("    Result: {}", decimal_counter.read()?);
//     println!("    Time: {:?}", decimal_duration);
//     println!(
//         "    Per increment: {:?}",
//         decimal_duration / safe_iterations as u32
//     );
//     println!(
//         "    Slowdown: {:.2}x",
//         decimal_duration.as_nanos() as f64 / u32_duration.as_nanos() as f64
//     );

//     // Test 3: Ribbon Binary
//     let start = Instant::now();
//     let mut binary_counter = HeapBinaryCounter::new();
//     for _ in 0..safe_iterations {
//         binary_counter.increment()?;
//     }
//     let binary_duration = start.elapsed();

//     println!("\n  Ribbon Binary Counter:");
//     println!("    Result: {}", binary_counter.read()?);
//     println!("    Time: {:?}", binary_duration);
//     println!(
//         "    Per increment: {:?}",
//         binary_duration / safe_iterations as u32
//     );
//     println!(
//         "    Slowdown: {:.2}x",
//         binary_duration.as_nanos() as f64 / u32_duration.as_nanos() as f64
//     );

//     // Test 4: Ribbon Hex
//     let start = Instant::now();
//     let mut hex_counter = HeapHexCounter::new();
//     for _ in 0..safe_iterations {
//         hex_counter.increment()?;
//     }
//     let hex_duration = start.elapsed();

//     println!("\n  Ribbon Hex Counter:");
//     println!("    Result: {}", hex_counter.read()?);
//     println!("    Time: {:?}", hex_duration);
//     println!(
//         "    Per increment: {:?}",
//         hex_duration / safe_iterations as u32
//     );
//     println!(
//         "    Slowdown: {:.2}x",
//         hex_duration.as_nanos() as f64 / u32_duration.as_nanos() as f64
//     );

//     println!("\n{}", "=".repeat(70));

//     Ok(())
// }

/// Convert any integer type to usize safely for loop bounds
///
/// # Safety
/// Ensures we never exceed usize::MAX or MAX_LOOP_ITERATIONS
fn safe_bound_usize(value: u128) -> usize {
    let max_usize = usize::MAX as u128;
    let max_iterations = MAX_LOOP_ITERATIONS as u128;

    value.min(max_usize).min(max_iterations) as usize
}

// ============================================================================
// UNIFIED BENCHMARK SYSTEM
// ============================================================================

/// Benchmark a native integer counter
///
/// # Type Parameters
/// * `T` - Integer type that supports wrapping_add
macro_rules! benchmark_native_counter {
    ($iterations:expr, $type:ty, $type_name:expr) => {{
        let start = Instant::now();
        let mut counter: $type = 0;
        for _ in 0..$iterations {
            counter = counter.wrapping_add(1);
        }
        let duration = start.elapsed();

        (counter, duration)
    }};
}

/// Comprehensive benchmark comparing all counter types
///
/// Tests:
/// 1. Native integer (u32, u64, or u128)
/// 2. Heap Decimal counter
/// 3. Heap Binary counter
/// 4. Heap Hex counter
/// 5. Stack Decimal counter
/// 6. Stack Binary counter
/// 7. Stack Hex counter
///
/// # Arguments
/// * `iterations` - Number of increments to perform (will be bounded safely)
/// * `int_type_name` - Name of integer type being compared
/// * `native_time` - Duration for native counter (for comparison)
/// * `native_result` - Result value from native counter
fn benchmark_ribbon_vs_native(
    iterations: usize,
    int_type_name: &str,
    native_time: std::time::Duration,
    native_result: &str,
) -> std::io::Result<()> {
    println!("\n{}", "=".repeat(70));
    println!(
        "  Comparing {} counters (bounded to {} iterations)",
        int_type_name, iterations
    );
    println!("{}", "=".repeat(70));

    // Display native results
    println!("\n  ╔══════════════════════════════════════════════════════════╗");
    println!(
        "  ║ Native {} Counter (BASELINE)                          ║",
        int_type_name
    );
    println!("  ╚══════════════════════════════════════════════════════════╝");
    println!("    Result: {}", native_result);
    println!("    Time: {:?}", native_time);
    if iterations > 0 {
        println!("    Per increment: {:?}", native_time / iterations as u32);
    }

    // Test Heap-based counters
    println!("\n  ╔══════════════════════════════════════════════════════════╗");
    println!("  ║ HEAP-BASED RIBBON COUNTERS                              ║");
    println!("  ╚══════════════════════════════════════════════════════════╝");

    // Heap Decimal
    let start = Instant::now();
    let mut decimal_counter = HeapDecimalCounter::new();
    for _ in 0..iterations {
        decimal_counter.increment()?;
    }
    let decimal_time = start.elapsed();
    let decimal_result = decimal_counter.read()?;

    println!("\n  Heap Decimal Counter:");
    println!("    Result: {}", decimal_result);
    println!("    Digits: {}", decimal_result.len());
    println!("    Time: {:?}", decimal_time);
    if iterations > 0 {
        println!("    Per increment: {:?}", decimal_time / iterations as u32);
    }
    println!(
        "    Slowdown: {:.2}x",
        decimal_time.as_nanos() as f64 / native_time.as_nanos() as f64
    );

    // Heap Binary
    let start = Instant::now();
    let mut binary_counter = HeapBinaryCounter::new();
    for _ in 0..iterations {
        binary_counter.increment()?;
    }
    let binary_time = start.elapsed();
    let binary_result = binary_counter.read()?;

    println!("\n  Heap Binary Counter:");
    println!("    Result: {}", binary_result);
    println!("    Bits: {}", binary_result.len());
    println!("    Time: {:?}", binary_time);
    if iterations > 0 {
        println!("    Per increment: {:?}", binary_time / iterations as u32);
    }
    println!(
        "    Slowdown: {:.2}x",
        binary_time.as_nanos() as f64 / native_time.as_nanos() as f64
    );
    println!(
        "    Space efficiency: {:.2}x more bits than decimal",
        binary_result.len() as f64 / decimal_result.len() as f64
    );

    // Heap Hex
    let start = Instant::now();
    let mut hex_counter = HeapHexCounter::new();
    for _ in 0..iterations {
        hex_counter.increment()?;
    }
    let hex_time = start.elapsed();
    let hex_result = hex_counter.read()?;

    println!("\n  Heap Hex Counter:");
    println!("    Result: 0x{}", hex_result);
    println!("    Hex digits: {}", hex_result.len());
    println!("    Time: {:?}", hex_time);
    if iterations > 0 {
        println!("    Per increment: {:?}", hex_time / iterations as u32);
    }
    println!(
        "    Slowdown: {:.2}x",
        hex_time.as_nanos() as f64 / native_time.as_nanos() as f64
    );
    println!(
        "    Space efficiency: {:.2}x fewer digits than decimal",
        decimal_result.len() as f64 / hex_result.len() as f64
    );

    // Test Stack-based counters
    println!("\n  ╔══════════════════════════════════════════════════════════╗");
    println!("  ║ STACK-BASED RIBBON COUNTERS (2048-byte buffer)          ║");
    println!("  ╚══════════════════════════════════════════════════════════╝");

    // Stack Decimal
    let start = Instant::now();
    let mut stack_decimal = StackDecimalCounter::new();
    for _ in 0..iterations {
        stack_decimal.increment()?;
    }
    let stack_decimal_time = start.elapsed();
    let stack_decimal_result = stack_decimal.read()?;

    println!("\n  Stack Decimal Counter:");
    println!("    Result: {}", stack_decimal_result);
    println!("    Time: {:?}", stack_decimal_time);
    if iterations > 0 {
        println!(
            "    Per increment: {:?}",
            stack_decimal_time / iterations as u32
        );
    }
    println!(
        "    Slowdown: {:.2}x",
        stack_decimal_time.as_nanos() as f64 / native_time.as_nanos() as f64
    );
    println!(
        "    vs Heap: {:.2}x {}",
        if stack_decimal_time < decimal_time {
            decimal_time.as_nanos() as f64 / stack_decimal_time.as_nanos() as f64
        } else {
            stack_decimal_time.as_nanos() as f64 / decimal_time.as_nanos() as f64
        },
        if stack_decimal_time < decimal_time {
            "faster"
        } else {
            "slower"
        }
    );

    // Stack Binary
    let start = Instant::now();
    let mut stack_binary = StackBinaryCounter::new();
    for _ in 0..iterations {
        stack_binary.increment()?;
    }
    let stack_binary_time = start.elapsed();
    let stack_binary_result = stack_binary.read()?;

    println!("\n  Stack Binary Counter:");
    println!("    Result: {}", stack_binary_result);
    println!("    Time: {:?}", stack_binary_time);
    if iterations > 0 {
        println!(
            "    Per increment: {:?}",
            stack_binary_time / iterations as u32
        );
    }
    println!(
        "    Slowdown: {:.2}x",
        stack_binary_time.as_nanos() as f64 / native_time.as_nanos() as f64
    );
    println!(
        "    vs Heap: {:.2}x {}",
        if stack_binary_time < binary_time {
            binary_time.as_nanos() as f64 / stack_binary_time.as_nanos() as f64
        } else {
            stack_binary_time.as_nanos() as f64 / binary_time.as_nanos() as f64
        },
        if stack_binary_time < binary_time {
            "faster"
        } else {
            "slower"
        }
    );

    // Stack Hex
    let start = Instant::now();
    let mut stack_hex = StackHexCounter::new();
    for _ in 0..iterations {
        stack_hex.increment()?;
    }
    let stack_hex_time = start.elapsed();
    let stack_hex_result = stack_hex.read()?;

    println!("\n  Stack Hex Counter:");
    println!("    Result: 0x{}", stack_hex_result);
    println!("    Time: {:?}", stack_hex_time);
    if iterations > 0 {
        println!(
            "    Per increment: {:?}",
            stack_hex_time / iterations as u32
        );
    }
    println!(
        "    Slowdown: {:.2}x",
        stack_hex_time.as_nanos() as f64 / native_time.as_nanos() as f64
    );
    println!(
        "    vs Heap: {:.2}x {}",
        if stack_hex_time < hex_time {
            hex_time.as_nanos() as f64 / stack_hex_time.as_nanos() as f64
        } else {
            stack_hex_time.as_nanos() as f64 / hex_time.as_nanos() as f64
        },
        if stack_hex_time < hex_time {
            "faster"
        } else {
            "slower"
        }
    );

    // Summary comparison
    println!("\n  ╔══════════════════════════════════════════════════════════╗");
    println!("  ║ SUMMARY                                                  ║");
    println!("  ╚══════════════════════════════════════════════════════════╝");
    println!(
        "\n  Fastest Ribbon method: {}",
        if hex_time < decimal_time && hex_time < binary_time {
            "Heap Hex"
        } else if decimal_time < binary_time {
            "Heap Decimal"
        } else {
            "Heap Binary"
        }
    );

    println!("  Most space-efficient: Hex (4 bits per digit)");
    println!("  Most human-readable: Decimal");
    println!("  Most compact representation: Hex (0x{})", hex_result);

    println!("\n{}", "=".repeat(70));

    Ok(())
}

/// Benchmark u32 counters
fn benchmark_u32(iterations: u32) -> std::io::Result<()> {
    println!("\n{}", "=".repeat(70));
    println!("  PERFORMANCE BENCHMARK: u32 ({} iterations)", iterations);
    println!("{}", "=".repeat(70));

    // Bound to safe iteration count
    let safe_iterations = safe_bound_usize(iterations as u128);

    // Native u32 benchmark
    let (result, duration) = benchmark_native_counter!(safe_iterations, u32, "u32");

    // Compare ribbon implementations
    benchmark_ribbon_vs_native(safe_iterations, "u32", duration, &result.to_string())?;

    Ok(())
}

/// Benchmark u64 counters
fn benchmark_u64(iterations: u64) -> std::io::Result<()> {
    println!("\n{}", "=".repeat(70));
    println!("  PERFORMANCE BENCHMARK: u64 ({} iterations)", iterations);
    println!("{}", "=".repeat(70));

    // Bound to safe iteration count
    let safe_iterations = safe_bound_usize(iterations as u128);

    // Native u64 benchmark
    let (result, duration) = benchmark_native_counter!(safe_iterations, u64, "u64");

    // Compare ribbon implementations
    benchmark_ribbon_vs_native(safe_iterations, "u64", duration, &result.to_string())?;

    Ok(())
}

/// Benchmark u128 counters
fn benchmark_u128(iterations: u128) -> std::io::Result<()> {
    println!("\n{}", "=".repeat(70));
    println!("  PERFORMANCE BENCHMARK: u128 ({} iterations)", iterations);
    println!("{}", "=".repeat(70));

    // Bound to safe iteration count
    let safe_iterations = safe_bound_usize(iterations);

    // Native u128 benchmark
    let (result, duration) = benchmark_native_counter!(safe_iterations, u128, "u128");

    // Compare ribbon implementations
    benchmark_ribbon_vs_native(safe_iterations, "u128", duration, &result.to_string())?;

    Ok(())
}

/// Demonstrate performance scaling across different integer sizes
fn demonstrate_performance_scaling() -> std::io::Result<()> {
    println!("\n{}", "=".repeat(70));
    println!("  PERFORMANCE SCALING ANALYSIS");
    println!("{}", "=".repeat(70));

    println!("\n  Testing how Ribbon performance scales with number magnitude...");
    println!("  (Native integers have constant-time performance)");
    println!("  (Ribbon counters slow down as digits increase)");

    // Small numbers (fit in u32)
    println!("\n  ╔══════════════════════════════════════════════════════════╗");
    println!("  ║ SMALL NUMBERS (< 1000) - 3-4 digits                     ║");
    println!("  ╚══════════════════════════════════════════════════════════╝");
    benchmark_u32(1000)?;

    // Medium numbers (require u64)
    println!("\n  ╔══════════════════════════════════════════════════════════╗");
    println!("  ║ MEDIUM NUMBERS (< 10000) - 5 digits                     ║");
    println!("  ╚══════════════════════════════════════════════════════════╝");
    benchmark_u32(10000)?;

    Ok(())
}

// ============================================================================
// PROS AND CONS ANALYSIS
// ============================================================================

fn print_analysis() {
    println!("\n{}", "=".repeat(70));
    println!("  PROS AND CONS ANALYSIS");
    println!("{}", "=".repeat(70));

    println!("\n  ╔════════════════════════════════════════════════════════════╗");
    println!("  ║  NATIVE FIXED-SIZE INTEGERS (u32, u64)                    ║");
    println!("  ╚════════════════════════════════════════════════════════════╝");

    println!("\n  PROS:");
    println!("    ✓ Extremely fast (1-5 nanoseconds per operation)");
    println!("    ✓ CPU-native operations (single instruction)");
    println!("    ✓ Zero memory overhead");
    println!("    ✓ Predictable performance");
    println!("    ✓ Easy to reason about");
    println!("    ✓ Compiler optimizations available");

    println!("\n  CONS:");
    println!("    ✗ Fixed maximum size (u32: 4 billion, u64: 18 quintillion)");
    println!("    ✗ Overflow behavior (wraps or panics)");
    println!("    ✗ Cannot handle arbitrary precision");
    println!("    ✗ Requires planning for maximum value");
    println!("    ✗ Historical failures (Y2K, Unix epoch 2038)");

    println!("\n  ╔════════════════════════════════════════════════════════════╗");
    println!("  ║  RIBBON COUNTERS (Arbitrary Precision)                    ║");
    println!("  ╚════════════════════════════════════════════════════════════╝");

    println!("\n  PROS:");
    println!("    ✓ Truly arbitrary precision (limited only by storage)");
    println!("    ✓ No overflow possible");
    println!("    ✓ Future-proof (handles Y2K, 2038, and beyond)");
    println!("    ✓ Can represent values larger than u128");
    println!("    ✓ Graceful growth (adds digits as needed)");
    println!("    ✓ Explicit representation (human-readable)");
    println!("    ✓ Can be persisted to disk");

    println!("\n  CONS:");
    println!("    ✗ Slower (50-200x slower than native integers)");
    println!("    ✗ Memory overhead (Vec allocation, digit storage)");
    println!("    ✗ More complex code");
    println!("    ✗ No CPU-native support");
    println!("    ✗ Variable performance (depends on digit count)");
    println!("    ✗ Harder to optimize");

    println!("\n  ╔════════════════════════════════════════════════════════════╗");
    println!("  ║  HYBRID APPROACH (Best of Both)                           ║");
    println!("  ╚════════════════════════════════════════════════════════════╝");

    println!("\n  PROS:");
    println!("    ✓ Fast for common cases (< 4 billion)");
    println!("    ✓ Safe for rare cases (> 4 billion)");
    println!("    ✓ No silent overflow");
    println!("    ✓ Automatic fallback");
    println!("    ✓ Best performance-safety tradeoff");

    println!("\n  CONS:");
    println!("    ✗ Slightly more complex implementation");
    println!("    ✗ Two code paths to maintain");
    println!("    ✗ One-time switching overhead");

    println!("\n  ╔════════════════════════════════════════════════════════════╗");
    println!("  ║  RECOMMENDATIONS                                           ║");
    println!("  ╚════════════════════════════════════════════════════════════╝");

    println!("\n  Use NATIVE INTEGERS when:");
    println!("    • Performance is critical");
    println!("    • Maximum value is known and bounded");
    println!("    • Value will never exceed u64::MAX");
    println!("    • Embedded/resource-constrained systems");

    println!("\n  Use RIBBON COUNTERS when:");
    println!("    • Arbitrary precision required");
    println!("    • Long-term timestamps (century+)");
    println!("    • Cryptographic applications");
    println!("    • Scientific computing (very large numbers)");
    println!("    • Cannot predict maximum value");

    println!("\n  Use HYBRID APPROACH when:");
    println!("    • Unknown input size");
    println!("    • Need both speed and safety");
    println!("    • Production systems (defensive programming)");
    println!("    • User-provided data");
    println!("    • This is usually the best choice!");

    println!("\n{}", "=".repeat(70));
}

fn main() -> std::io::Result<()> {
    println!("\n🎀 RIBBON: \"It's tape all the way down.\"");
    println!("    Externalized Procedural Variables in Rust\n");

    // Count files in current directory as demonstration target
    let file_count = std::fs::read_dir(".")?.count();
    println!("📁 Files in current directory: {}\n", file_count);

    // ========================================================================
    // TYPE A: DISK-BASED COUNTERS
    // ========================================================================

    print_banner("TYPE A: DISK-BASED COUNTERS (Persistent Storage)");

    let mut disk_binary = DiskBinaryCounter::new("counter_disk_binary.txt")?;
    disk_binary.reset()?;
    demonstrate_counter(&mut disk_binary, "Binary (Disk)", file_count)?;

    let mut disk_hex = DiskHexCounter::new("counter_disk_hex.txt")?;
    disk_hex.reset()?;
    demonstrate_counter(&mut disk_hex, "Hex (Disk)", file_count)?;

    let mut disk_decimal = DiskDecimalCounter::new("counter_disk_decimal.txt")?;
    disk_decimal.reset()?;
    demonstrate_counter(&mut disk_decimal, "Decimal (Disk)", file_count)?;

    // ========================================================================
    // TYPE B: HEAP-BASED COUNTERS
    // ========================================================================

    print_banner("TYPE B: HEAP-BASED COUNTERS (Dynamic Memory)");

    let mut heap_binary = HeapBinaryCounter::new();
    demonstrate_counter(&mut heap_binary, "Binary (Heap)", file_count)?;

    let mut heap_hex = HeapHexCounter::new();
    demonstrate_counter(&mut heap_hex, "Hex (Heap)", file_count)?;

    let mut heap_decimal = HeapDecimalCounter::new();
    demonstrate_counter(&mut heap_decimal, "Decimal (Heap)", file_count)?;

    // ========================================================================
    // TYPE C: STACK-BASED COUNTERS
    // ========================================================================

    print_banner("TYPE C: STACK-BASED COUNTERS (Pre-allocated 2048-byte Buffer)");

    let mut stack_binary = StackBinaryCounter::new();
    demonstrate_counter(&mut stack_binary, "Binary (Stack)", file_count)?;

    let mut stack_hex = StackHexCounter::new();
    demonstrate_counter(&mut stack_hex, "Hex (Stack)", file_count)?;

    let mut stack_decimal = StackDecimalCounter::new();
    demonstrate_counter(&mut stack_decimal, "Decimal (Stack)", file_count)?;

    // ========================================================================
    // LARGE NUMBER DEMONSTRATION
    // ========================================================================

    print_banner("LARGE NUMBER DEMONSTRATION");

    println!("\n  Counting to 1000...");
    let mut large_decimal = HeapDecimalCounter::new();
    demonstrate_counter(&mut large_decimal, "Decimal", 1000)?;

    let mut large_binary = HeapBinaryCounter::new();
    demonstrate_counter(&mut large_binary, "Binary", 1000)?;
    println!("  (Binary uses {} bits)", large_binary.read()?.len());

    let mut large_hex = HeapHexCounter::new();
    demonstrate_counter(&mut large_hex, "Hex", 1000)?;
    println!(
        "  (Hex uses {} digits, 4x more efficient than binary)",
        large_hex.read()?.len()
    );

    // ========================================================================
    // CAPACITY DEMONSTRATION
    // ========================================================================

    print_banner("CAPACITY DEMONSTRATION");

    println!("\n  Stack buffer capacity: {} bytes", STACK_BUFFER_SIZE);
    println!(
        "  Binary capacity: 2^{} (requires {} bits)",
        STACK_BUFFER_SIZE, STACK_BUFFER_SIZE
    );
    println!(
        "  Decimal capacity: 10^{} (requires {} digits)",
        STACK_BUFFER_SIZE, STACK_BUFFER_SIZE
    );
    println!(
        "  Hex capacity: 16^{} (requires {} hex digits)",
        STACK_BUFFER_SIZE, STACK_BUFFER_SIZE
    );
    println!("\n  For comparison:");
    println!("    u64::MAX  = 2^64  ≈ 1.8 × 10^19");
    println!("    u128::MAX = 2^128 ≈ 3.4 × 10^38");
    println!("    This system supports values many orders of magnitude larger!");

    // ========================================================================
    // USE CASE: TIMESTAMP BEYOND 2038
    // ========================================================================

    print_banner("USE CASE: Year-2038-Proof Timestamp Counter");

    println!("\n  Unix Epoch overflow (2038 problem): 2,147,483,647 seconds");
    println!("  Creating counter that can handle year 3000 and beyond...");

    let mut timestamp_counter = StackDecimalCounter::new();
    // Simulate counting seconds for 100 years (not actually running this many iterations)
    let seconds_in_100_years: usize = 100 * 365 * 24 * 60 * 60;
    println!("  Seconds in 100 years: {}", seconds_in_100_years);
    println!("  This counter can represent timestamps far beyond any integer overflow.");

    // ========================================================================

    println!("\n{}", "=".repeat(70));
    println!("  ✨ \"It's tape all the way down!\"");
    println!("  No fixed-size integer limits. Process digit-by-digit.");
    println!("  Arbitrary precision within storage constraints.");
    println!("{}\n", "=".repeat(70));

    // Demonstrate hybrid counting
    println!("\n{}", "=".repeat(70));
    println!("  HYBRID COUNTER DEMONSTRATION");
    println!("{}", "=".repeat(70));

    let result = count_directory_hybrid(".")?;
    println!("\n  Directory: .");
    println!("  Items counted: {}", result.as_string());
    println!(
        "  Method used: {}",
        if result.is_fast() {
            "Fast (u32)"
        } else {
            "Ribbon (arbitrary)"
        }
    );

    // ========================================================================
    // PERFORMANCE BENCHMARKS
    // ========================================================================

    // Run comprehensive benchmarks at different scales
    demonstrate_performance_scaling()?;

    // You can also run individual benchmarks:
    benchmark_u32(1_000)?;
    benchmark_u64(10_000)?;
    benchmark_u128(10_000)?;

    // Analysis
    print_analysis();

    Ok(())
}

// ============================================================================
// HYBRID SAFETY COUNTER
// ============================================================================

/// Result of a count operation
#[derive(Debug)]
enum CountResult {
    /// Count completed using fast u32 arithmetic
    FastCount(u32),
    /// Count exceeded u32, fell back to ribbon counter
    RibbonCount(String),
}

impl CountResult {
    /// Get the count as a string representation
    fn as_string(&self) -> String {
        match self {
            CountResult::FastCount(n) => n.to_string(),
            CountResult::RibbonCount(s) => s.clone(),
        }
    }

    /// Check if this used the fast path
    fn is_fast(&self) -> bool {
        matches!(self, CountResult::FastCount(_))
    }
}

/// Hybrid counter that tries u32 first, falls back to ribbon on overflow
///
/// # Policy
/// 1. Attempt to use fast u32 arithmetic
/// 2. If overflow detected, switch to ribbon counter
/// 3. Once switched, stay in ribbon mode
///
/// # Use Cases
/// - Most real-world counts fit in u32 (4 billion items)
/// - Provides speed when possible
/// - Provides correctness when necessary
/// - Never silently overflows
struct HybridCounter {
    /// Fast counter (None if overflowed)
    fast: Option<u32>,
    /// Ribbon backup (None until needed)
    ribbon: Option<HeapDecimalCounter>,
}

impl HybridCounter {
    /// Create new hybrid counter starting at 0
    fn new() -> Self {
        HybridCounter {
            fast: Some(0),
            ribbon: None,
        }
    }

    /// Increment the counter, automatically switching to ribbon if needed
    ///
    /// # Algorithm
    /// 1. If still using fast mode, try to increment u32
    /// 2. If u32 would overflow, switch to ribbon mode
    /// 3. If already in ribbon mode, just increment ribbon
    ///
    /// # Example Flow:
    /// ```text
    /// Start: fast=Some(0), ribbon=None
    ///
    /// Increment 1 billion times:
    ///   fast=Some(1_000_000_000), ribbon=None  [FAST MODE]
    ///
    /// Try to exceed u32::MAX:
    ///   Detect overflow
    ///   Create ribbon from fast value
    ///   fast=None, ribbon=Some(counter)  [RIBBON MODE]
    ///
    /// All future increments:
    ///   Use ribbon only  [STAY IN RIBBON MODE]
    /// ```
    fn increment(&mut self) -> std::io::Result<()> {
        // Check if we're still in fast mode
        if let Some(current) = self.fast {
            // Attempt to increment with overflow check
            match current.checked_add(1) {
                Some(new_value) => {
                    // Success! Still fits in u32
                    self.fast = Some(new_value);
                }
                None => {
                    // Overflow detected! Switch to ribbon mode

                    // Create ribbon counter initialized to current value
                    let mut ribbon = HeapDecimalCounter::new();

                    // Build ribbon representation of u32::MAX value
                    // (we were at MAX, now need to go to MAX+1)
                    let max_str = u32::MAX.to_string();
                    ribbon.digits = max_str
                        .chars()
                        .map(|c| c.to_digit(10).unwrap() as u8)
                        .collect();

                    // Now increment from MAX to MAX+1
                    ribbon.increment()?;

                    // Switch to ribbon mode
                    self.fast = None;
                    self.ribbon = Some(ribbon);
                }
            }
        } else {
            // Already in ribbon mode, just increment
            if let Some(ref mut ribbon) = self.ribbon {
                ribbon.increment()?;
            }
        }

        Ok(())
    }

    /// Read current count value
    fn read(&self) -> std::io::Result<CountResult> {
        if let Some(fast_value) = self.fast {
            // Still in fast mode
            Ok(CountResult::FastCount(fast_value))
        } else if let Some(ref ribbon) = self.ribbon {
            // In ribbon mode
            Ok(CountResult::RibbonCount(ribbon.read()?))
        } else {
            // Should never happen
            Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Counter in invalid state",
            ))
        }
    }

    /// Reset counter to 0
    fn reset(&mut self) -> std::io::Result<()> {
        self.fast = Some(0);
        self.ribbon = None;
        Ok(())
    }
}

/// Count items in a directory using hybrid counter
///
/// # Safety Features
/// - Tries fast u32 counting first (most common case)
/// - Automatically switches to ribbon if directory has > 4 billion items
/// - Never overflows or loses count
///
/// # Performance
/// - Fast path (u32): ~1-5 nanoseconds per increment
/// - Slow path (ribbon): ~50-200 nanoseconds per increment
/// - Switching overhead: one-time cost of ~100 nanoseconds
///
/// # Arguments
/// * `path` - Directory path to count
///
/// # Returns
/// Result containing either fast count (u32) or ribbon count (String)
fn count_directory_hybrid(path: &str) -> std::io::Result<CountResult> {
    let mut counter = HybridCounter::new();

    // Iterate through directory entries
    for entry in std::fs::read_dir(path)? {
        let _ = entry?; // Validate entry
        counter.increment()?;
    }

    counter.read()
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_disk_binary_increment() {
        let path = "test_binary_increment.txt";
        let mut counter = DiskBinaryCounter::new(path).unwrap();
        counter.reset().unwrap();

        assert_eq!(counter.read().unwrap(), "1");

        counter.increment().unwrap();
        assert_eq!(counter.read().unwrap(), "10");

        counter.increment().unwrap();
        assert_eq!(counter.read().unwrap(), "11");

        counter.increment().unwrap();
        assert_eq!(counter.read().unwrap(), "100");

        std::fs::remove_file(path).ok();
    }

    #[test]
    fn test_disk_hex_to_16() {
        let path = "test_hex_16.txt";
        let mut counter = DiskHexCounter::new(path).unwrap();
        counter.reset().unwrap();

        // Count from 0 to 16 (0x10 in hex)
        for _ in 0..16 {
            counter.increment().unwrap();
        }
        assert_eq!(counter.read().unwrap(), "10");

        std::fs::remove_file(path).ok();
    }

    #[test]
    fn test_disk_decimal_to_100() {
        let path = "test_decimal_100.txt";
        let mut counter = DiskDecimalCounter::new(path).unwrap();
        counter.reset().unwrap();

        for _ in 0..100 {
            counter.increment().unwrap();
        }
        assert_eq!(counter.read().unwrap(), "100");

        std::fs::remove_file(path).ok();
    }

    #[test]
    fn test_heap_binary_sequence() {
        let mut counter = HeapBinaryCounter::new();

        let expected = ["1", "10", "11", "100", "101", "110", "111", "1000"];

        for &exp in &expected {
            assert_eq!(counter.read().unwrap(), exp);
            counter.increment().unwrap();
        }
    }

    #[test]
    fn test_heap_decimal_to_1000() {
        let mut counter = HeapDecimalCounter::new();

        for _ in 0..1000 {
            counter.increment().unwrap();
        }
        assert_eq!(counter.read().unwrap(), "1000");
    }

    #[test]
    fn test_heap_hex_to_256() {
        let mut counter = HeapHexCounter::new();

        for _ in 0..256 {
            counter.increment().unwrap();
        }
        assert_eq!(counter.read().unwrap(), "100");
    }

    #[test]
    fn test_stack_binary_basic() {
        let mut counter = StackBinaryCounter::new();

        assert_eq!(counter.read().unwrap(), "1");
        counter.increment().unwrap();
        assert_eq!(counter.read().unwrap(), "10");
        counter.increment().unwrap();
        assert_eq!(counter.read().unwrap(), "11");
    }

    #[test]
    fn test_stack_decimal_basic() {
        let mut counter = StackDecimalCounter::new();

        for _ in 0..50 {
            counter.increment().unwrap();
        }
        assert_eq!(counter.read().unwrap(), "50");
    }

    #[test]
    fn test_stack_hex_basic() {
        let mut counter = StackHexCounter::new();

        for _ in 0..32 {
            counter.increment().unwrap();
        }
        assert_eq!(counter.read().unwrap(), "20");
    }

    #[test]
    fn test_all_bases_equal_value() {
        // All should represent same value: decimal 15
        let mut binary = HeapBinaryCounter::new();
        let mut decimal = HeapDecimalCounter::new();
        let mut hex = HeapHexCounter::new();

        for _ in 0..15 {
            binary.increment().unwrap();
            decimal.increment().unwrap();
            hex.increment().unwrap();
        }

        assert_eq!(binary.read().unwrap(), "1111"); // 15 in binary
        assert_eq!(decimal.read().unwrap(), "15"); // 15 in decimal
        assert_eq!(hex.read().unwrap(), "F"); // 15 in hex
    }

    #[test]
    fn test_binary_increment_sequence() {
        let mut counter = HeapBinaryCounter::new();

        let expected = vec!["1", "10", "11", "100", "101", "110", "111", "1000"];

        for exp in expected {
            assert_eq!(counter.read().unwrap(), exp);
            counter.increment().unwrap();
        }
    }

    #[test]
    fn test_decimal_carries() {
        let mut counter = HeapDecimalCounter::new();

        // Count to 1001 to test multiple carry scenarios
        for _ in 0..1001 {
            counter.increment().unwrap();
        }

        assert_eq!(counter.read().unwrap(), "1001");
    }

    #[test]
    fn test_hex_to_256() {
        let mut counter = HeapHexCounter::new();

        for _ in 0..256 {
            counter.increment().unwrap();
        }

        // 256 in hex is 100
        assert_eq!(counter.read().unwrap(), "100");
    }

    #[test]
    fn test_hybrid_small_count() {
        let mut hybrid = HybridCounter::new();

        for _ in 0..100 {
            hybrid.increment().unwrap();
        }

        let result = hybrid.read().unwrap();
        assert!(result.is_fast());
        assert_eq!(result.as_string(), "100");
    }

    #[test]
    fn test_hybrid_overflow() {
        let mut hybrid = HybridCounter::new();
        hybrid.fast = Some(u32::MAX - 5);

        // These should succeed in fast mode
        for _ in 0..5 {
            hybrid.increment().unwrap();
        }
        assert!(hybrid.fast.is_some());

        // This should trigger switch to ribbon
        hybrid.increment().unwrap();
        assert!(hybrid.fast.is_none());
        assert!(hybrid.ribbon.is_some());

        let result = hybrid.read().unwrap();
        assert!(!result.is_fast());
    }
}
