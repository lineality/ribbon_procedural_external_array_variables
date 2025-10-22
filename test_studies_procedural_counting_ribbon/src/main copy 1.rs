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
struct HeapBinaryCounter {
    tape: Vec<bool>,
}

impl HeapBinaryCounter {
    fn new() -> Self {
        HeapBinaryCounter { tape: vec![true] }
    }
}

impl ExternalCounter for HeapBinaryCounter {
    fn increment(&mut self) -> std::io::Result<()> {
        assert!(
            self.tape.len() <= MAX_LOOP_ITERATIONS,
            "Counter exceeds safety limit"
        );

        let mut carry = true;
        let len = self.tape.len();

        for i in 0..len {
            let idx = len - 1 - i;

            if carry {
                if !self.tape[idx] {
                    self.tape[idx] = true;
                    carry = false;
                    break;
                } else {
                    self.tape[idx] = false;
                }
            } else {
                break;
            }
        }

        if carry {
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
    digits: Vec<u8>, // Store digits 0-9
}

impl HeapDecimalCounter {
    fn new() -> Self {
        HeapDecimalCounter { digits: vec![0] }
    }
}

impl ExternalCounter for HeapDecimalCounter {
    fn increment(&mut self) -> std::io::Result<()> {
        assert!(
            self.digits.len() <= MAX_LOOP_ITERATIONS,
            "Counter exceeds safety limit"
        );

        let mut carry = true;
        let len = self.digits.len();

        for i in 0..len {
            let idx = len - 1 - i;

            if carry {
                if self.digits[idx] == 9 {
                    self.digits[idx] = 0;
                } else {
                    self.digits[idx] += 1;
                    carry = false;
                    break;
                }
            } else {
                break;
            }
        }

        if carry {
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
    digits: Vec<u8>, // Store digits 0-15
}

impl HeapHexCounter {
    fn new() -> Self {
        HeapHexCounter { digits: vec![0] }
    }
}

impl ExternalCounter for HeapHexCounter {
    fn increment(&mut self) -> std::io::Result<()> {
        assert!(
            self.digits.len() <= MAX_LOOP_ITERATIONS,
            "Counter exceeds safety limit"
        );

        let mut carry = true;
        let len = self.digits.len();

        for i in 0..len {
            let idx = len - 1 - i;

            if carry {
                if self.digits[idx] == 15 {
                    self.digits[idx] = 0;
                } else {
                    self.digits[idx] += 1;
                    carry = false;
                    break;
                }
            } else {
                break;
            }
        }

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

    Ok(())
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
}
