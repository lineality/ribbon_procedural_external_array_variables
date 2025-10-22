// src/lib.rs

use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::Path;

/// Trait for externalized counter operations
pub trait ExternalCounter {
    fn increment(&mut self) -> std::io::Result<()>;
    fn read(&self) -> std::io::Result<String>;
    fn reset(&mut self) -> std::io::Result<()>;
}

/// Disk-based binary counter
pub struct DiskBinaryCounter {
    path: String,
}

impl DiskBinaryCounter {
    pub fn new(path: &str) -> std::io::Result<Self> {
        let counter = DiskBinaryCounter {
            path: path.to_string(),
        };

        // Initialize with "1" if file doesn't exist
        if !Path::new(path).exists() {
            let mut file = File::create(path)?;
            file.write_all(b"1")?;
        }

        Ok(counter)
    }

    /// Increment binary number stored as ASCII '0' and '1' characters
    fn increment_binary_tape(&mut self) -> std::io::Result<()> {
        let mut file = OpenOptions::new().read(true).write(true).open(&self.path)?;

        let mut contents = String::new();
        file.read_to_string(&mut contents)?;

        let mut digits: Vec<char> = contents.trim().chars().collect();

        // Add carry from right to left
        let mut carry = true;
        for i in (0..digits.len()).rev() {
            if carry {
                if digits[i] == '0' {
                    digits[i] = '1';
                    carry = false;
                } else {
                    digits[i] = '0';
                }
            }
        }

        // If still carrying, prepend a '1'
        if carry {
            digits.insert(0, '1');
        }

        // Write back
        file.set_len(0)?;
        file.seek(SeekFrom::Start(0))?;
        file.write_all(digits.iter().collect::<String>().as_bytes())?;

        Ok(())
    }
}

impl ExternalCounter for DiskBinaryCounter {
    fn increment(&mut self) -> std::io::Result<()> {
        self.increment_binary_tape()
    }

    fn read(&self) -> std::io::Result<String> {
        std::fs::read_to_string(&self.path)
    }

    fn reset(&mut self) -> std::io::Result<()> {
        let mut file = File::create(&self.path)?;
        file.write_all(b"1")?;
        Ok(())
    }
}

/// Disk-based hexadecimal counter
pub struct DiskHexCounter {
    path: String,
}

impl DiskHexCounter {
    pub fn new(path: &str) -> std::io::Result<Self> {
        let counter = DiskHexCounter {
            path: path.to_string(),
        };

        if !Path::new(path).exists() {
            let mut file = File::create(path)?;
            file.write_all(b"1")?;
        }

        Ok(counter)
    }

    fn hex_char_to_value(c: char) -> u8 {
        match c {
            '0'..='9' => c as u8 - b'0',
            'A'..='F' => c as u8 - b'A' + 10,
            'a'..='f' => c as u8 - b'a' + 10,
            _ => 0,
        }
    }

    fn value_to_hex_char(v: u8) -> char {
        match v {
            0..=9 => (b'0' + v) as char,
            10..=15 => (b'A' + v - 10) as char,
            _ => '0',
        }
    }

    fn increment_hex_tape(&mut self) -> std::io::Result<()> {
        let mut file = OpenOptions::new().read(true).write(true).open(&self.path)?;

        let mut contents = String::new();
        file.read_to_string(&mut contents)?;

        let mut digits: Vec<char> = contents.trim().chars().collect();

        let mut carry = 1u8;
        for i in (0..digits.len()).rev() {
            if carry > 0 {
                let mut val = Self::hex_char_to_value(digits[i]) + carry;
                if val >= 16 {
                    val = 0;
                    carry = 1;
                } else {
                    carry = 0;
                }
                digits[i] = Self::value_to_hex_char(val);
            }
        }

        if carry > 0 {
            digits.insert(0, '1');
        }

        file.set_len(0)?;
        file.seek(SeekFrom::Start(0))?;
        file.write_all(digits.iter().collect::<String>().as_bytes())?;

        Ok(())
    }
}

impl ExternalCounter for DiskHexCounter {
    fn increment(&mut self) -> std::io::Result<()> {
        self.increment_hex_tape()
    }

    fn read(&self) -> std::io::Result<String> {
        std::fs::read_to_string(&self.path)
    }

    fn reset(&mut self) -> std::io::Result<()> {
        let mut file = File::create(&self.path)?;
        file.write_all(b"1")?;
        Ok(())
    }
}

/// Disk-based decimal counter
pub struct DiskDecimalCounter {
    path: String,
}

impl DiskDecimalCounter {
    pub fn new(path: &str) -> std::io::Result<Self> {
        let counter = DiskDecimalCounter {
            path: path.to_string(),
        };

        if !Path::new(path).exists() {
            let mut file = File::create(path)?;
            file.write_all(b"0")?;
        }

        Ok(counter)
    }

    fn increment_decimal_tape(&mut self) -> std::io::Result<()> {
        let mut file = OpenOptions::new().read(true).write(true).open(&self.path)?;

        let mut contents = String::new();
        file.read_to_string(&mut contents)?;

        let mut digits: Vec<char> = contents.trim().chars().collect();

        let mut carry = true;
        for i in (0..digits.len()).rev() {
            if carry {
                let digit = digits[i].to_digit(10).unwrap_or(0);
                if digit == 9 {
                    digits[i] = '0';
                } else {
                    digits[i] = char::from_digit(digit + 1, 10).unwrap();
                    carry = false;
                }
            }
        }

        if carry {
            digits.insert(0, '1');
        }

        file.set_len(0)?;
        file.seek(SeekFrom::Start(0))?;
        file.write_all(digits.iter().collect::<String>().as_bytes())?;

        Ok(())
    }
}

impl ExternalCounter for DiskDecimalCounter {
    fn increment(&mut self) -> std::io::Result<()> {
        self.increment_decimal_tape()
    }

    fn read(&self) -> std::io::Result<String> {
        std::fs::read_to_string(&self.path)
    }

    fn reset(&mut self) -> std::io::Result<()> {
        let mut file = File::create(&self.path)?;
        file.write_all(b"0")?;
        Ok(())
    }
}

/// Heap-based binary counter (using Vec<bool>)
pub struct HeapBinaryCounter {
    tape: Vec<bool>,
}

impl HeapBinaryCounter {
    pub fn new() -> Self {
        HeapBinaryCounter { tape: vec![true] }
    }

    fn to_string(&self) -> String {
        self.tape
            .iter()
            .map(|&b| if b { '1' } else { '0' })
            .collect()
    }
}

impl ExternalCounter for HeapBinaryCounter {
    fn increment(&mut self) -> std::io::Result<()> {
        let mut carry = true;

        for i in (0..self.tape.len()).rev() {
            if carry {
                if !self.tape[i] {
                    self.tape[i] = true;
                    carry = false;
                } else {
                    self.tape[i] = false;
                }
            }
        }

        if carry {
            self.tape.insert(0, true);
        }

        Ok(())
    }

    fn read(&self) -> std::io::Result<String> {
        Ok(self.to_string())
    }

    fn reset(&mut self) -> std::io::Result<()> {
        self.tape = vec![true];
        Ok(())
    }
}

/// Heap-based decimal counter
pub struct HeapDecimalCounter {
    digits: Vec<u8>, // Store digits 0-9
}

impl HeapDecimalCounter {
    pub fn new() -> Self {
        HeapDecimalCounter { digits: vec![0] }
    }

    fn to_string(&self) -> String {
        self.digits
            .iter()
            .map(|&d| char::from_digit(d as u32, 10).unwrap())
            .collect()
    }
}

impl ExternalCounter for HeapDecimalCounter {
    fn increment(&mut self) -> std::io::Result<()> {
        let mut carry = true;

        for i in (0..self.digits.len()).rev() {
            if carry {
                if self.digits[i] == 9 {
                    self.digits[i] = 0;
                } else {
                    self.digits[i] += 1;
                    carry = false;
                }
            }
        }

        if carry {
            self.digits.insert(0, 1);
        }

        Ok(())
    }

    fn read(&self) -> std::io::Result<String> {
        Ok(self.to_string())
    }

    fn reset(&mut self) -> std::io::Result<()> {
        self.digits = vec![0];
        Ok(())
    }
}

/// Heap-based hexadecimal counter
pub struct HeapHexCounter {
    digits: Vec<u8>, // Store digits 0-15
}

impl HeapHexCounter {
    pub fn new() -> Self {
        HeapHexCounter { digits: vec![1] }
    }

    fn to_string(&self) -> String {
        self.digits
            .iter()
            .map(|&d| char::from_digit(d as u32, 16).unwrap().to_ascii_uppercase())
            .collect()
    }
}

impl ExternalCounter for HeapHexCounter {
    fn increment(&mut self) -> std::io::Result<()> {
        let mut carry = true;

        for i in (0..self.digits.len()).rev() {
            if carry {
                if self.digits[i] == 15 {
                    self.digits[i] = 0;
                } else {
                    self.digits[i] += 1;
                    carry = false;
                }
            }
        }

        if carry {
            self.digits.insert(0, 1);
        }

        Ok(())
    }

    fn read(&self) -> std::io::Result<String> {
        Ok(self.to_string())
    }

    fn reset(&mut self) -> std::io::Result<()> {
        self.digits = vec![1];
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_disk_binary_counter() {
        let path = "test_binary.txt";
        let mut counter = DiskBinaryCounter::new(path).unwrap();

        assert_eq!(counter.read().unwrap().trim(), "1");

        counter.increment().unwrap();
        assert_eq!(counter.read().unwrap().trim(), "10");

        counter.increment().unwrap();
        assert_eq!(counter.read().unwrap().trim(), "11");

        counter.increment().unwrap();
        assert_eq!(counter.read().unwrap().trim(), "100");

        fs::remove_file(path).ok();
    }

    #[test]
    fn test_disk_hex_counter() {
        let path = "test_hex.txt";
        let mut counter = DiskHexCounter::new(path).unwrap();

        for _ in 0..15 {
            counter.increment().unwrap();
        }
        assert_eq!(counter.read().unwrap().trim(), "10");

        fs::remove_file(path).ok();
    }

    #[test]
    fn test_disk_decimal_counter() {
        let path = "test_decimal.txt";
        let mut counter = DiskDecimalCounter::new(path).unwrap();

        for _ in 0..10 {
            counter.increment().unwrap();
        }
        assert_eq!(counter.read().unwrap().trim(), "10");

        fs::remove_file(path).ok();
    }

    #[test]
    fn test_heap_binary_counter() {
        let mut counter = HeapBinaryCounter::new();

        assert_eq!(counter.read().unwrap(), "1");
        counter.increment().unwrap();
        assert_eq!(counter.read().unwrap(), "10");
        counter.increment().unwrap();
        assert_eq!(counter.read().unwrap(), "11");
        counter.increment().unwrap();
        assert_eq!(counter.read().unwrap(), "100");
    }

    #[test]
    fn test_heap_decimal_counter() {
        let mut counter = HeapDecimalCounter::new();

        for _ in 0..100 {
            counter.increment().unwrap();
        }
        assert_eq!(counter.read().unwrap(), "100");
    }

    #[test]
    fn test_heap_hex_counter() {
        let mut counter = HeapHexCounter::new();

        for _ in 0..255 {
            counter.increment().unwrap();
        }
        assert_eq!(counter.read().unwrap(), "100");
    }
}

// src/main.rs

// use ribbon::{
//     DiskBinaryCounter, DiskDecimalCounter, DiskHexCounter, ExternalCounter, HeapBinaryCounter,
//     HeapDecimalCounter, HeapHexCounter,
// };
use std::fs;

fn main() -> std::io::Result<()> {
    println!("🎀 Ribbon - Externalized Procedural Variables\n");

    // Demonstration: Count files in current directory
    let entries = fs::read_dir(".")?.count();

    println!("=== Disk-Based Counters ===\n");

    // Binary counter on disk
    println!("Binary Counter (Disk):");
    let mut binary = DiskBinaryCounter::new("counter_binary.txt")?;
    binary.reset()?;
    for _ in 0..entries {
        binary.increment()?;
    }
    println!("  Files counted: {} (binary)", binary.read()?.trim());

    // Hexadecimal counter on disk
    println!("\nHexadecimal Counter (Disk):");
    let mut hex = DiskHexCounter::new("counter_hex.txt")?;
    hex.reset()?;
    for _ in 0..entries {
        hex.increment()?;
    }
    println!("  Files counted: {} (hex)", hex.read()?.trim());

    // Decimal counter on disk
    println!("\nDecimal Counter (Disk):");
    let mut decimal = DiskDecimalCounter::new("counter_decimal.txt")?;
    decimal.reset()?;
    for _ in 0..entries {
        decimal.increment()?;
    }
    println!("  Files counted: {} (decimal)", decimal.read()?.trim());

    println!("\n=== Heap-Based Counters ===\n");

    // Binary counter in heap
    println!("Binary Counter (Heap):");
    let mut heap_binary = HeapBinaryCounter::new();
    for _ in 0..entries {
        heap_binary.increment()?;
    }
    println!("  Files counted: {} (binary)", heap_binary.read()?);

    // Decimal counter in heap
    println!("\nDecimal Counter (Heap):");
    let mut heap_decimal = HeapDecimalCounter::new();
    for _ in 0..entries {
        heap_decimal.increment()?;
    }
    println!("  Files counted: {} (decimal)", heap_decimal.read()?);

    // Hexadecimal counter in heap
    println!("\nHexadecimal Counter (Heap):");
    let mut heap_hex = HeapHexCounter::new();
    for _ in 0..entries {
        heap_hex.increment()?;
    }
    println!("  Files counted: {} (hex)", heap_hex.read()?);

    println!("\n=== Large Number Demonstration ===\n");

    // Demonstrate counting to 1000
    let mut large_counter = HeapDecimalCounter::new();
    for _ in 0..1000 {
        large_counter.increment()?;
    }
    println!("Counted to: {}", large_counter.read()?);

    // Binary representation
    let mut large_binary = HeapBinaryCounter::new();
    for _ in 0..1000 {
        large_binary.increment()?;
    }
    println!("In binary: {}", large_binary.read()?);
    println!("Bits used: {}", large_binary.read()?.len());

    println!("\n✨ \"It's tape all the way down!\"");

    Ok(())
}
