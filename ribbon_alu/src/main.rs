//! Binary multiplication using instruction recording and playback
//!
//! Strategy:
//! 1. Read multiplier, emit ADD/DOUBLE instructions
//! 2. Execute instructions on accumulator
//! 3. Each instruction processes digits one-at-a-time
//!
//! Memory: O(1) - only current digit + carry state
//! Time: Multiple passes through files
//!

/*
START
├── Read: multiplier_file
├── Create: instructions.bin
│
├── Create: accumulator.bin ← "0"
│
├── Read: instructions.bin (sequential)
│   ├── For each DOUBLE instruction:
│   │   └── Append '0' to accumulator.bin
│   │
│   └── For each ADD instruction:
│       ├── Read: accumulator.bin + multiplicand_file
│       ├── Create: temp_add_result.bin
│       ├── Delete: accumulator.bin
│       └── Rename: temp_add_result.bin → accumulator.bin
│
├── Copy: accumulator.bin → result.bin
│
END
# Binary Multiplication Algorithm - Tape Machine Implementation

## Overview

This document outlines the procedural, constant-memory multiplication algorithm used to multiply arbitrarily large binary numbers stored in files.

---

## Algorithm Strategy: Horner's Method with Instruction Recording

The algorithm uses a **two-phase approach**:

### Phase 1: Instruction Generation
Read the multiplier file once, emit a sequence of primitive operations.

### Phase 2: Instruction Execution
Execute the recorded operations one-by-one on the multiplicand.

**Key Property:** At no point is any complete number loaded into a single memory variable. All operations process digit-by-digit.

---

## Phase 1: Instruction Generation

### Input
- `multiplier_file`: Binary number stored as ASCII '0' and '1' characters, MSB-first (leftmost digit is most significant)

### Output
- `instruction_file`: Sequence of operation codes (bytes)

### Process

Read multiplier **left-to-right** (MSB to LSB), one bit at a time:

```
For first bit:
  IF bit == '1':
    EMIT: ADD
  ELSE:
    (emit nothing - accumulator stays at 0)

For each subsequent bit:
  EMIT: DOUBLE
  IF bit == '1':
    EMIT: ADD
```

### Example

**Multiplier:** `101` (5 in decimal)

```
Position 0 (leftmost): bit='1'
  → EMIT: ADD

Position 1: bit='0'
  → EMIT: DOUBLE
  (no ADD)

Position 2 (rightmost): bit='1'
  → EMIT: DOUBLE
  → EMIT: ADD
```

**Instruction tape:** `[ADD, DOUBLE, DOUBLE, ADD]`

### Memory Used
- Current bit: 1 byte
- Output buffer: ~8KB (standard BufWriter)
- **Total: Constant, regardless of multiplier size**

---

## Phase 2: Instruction Execution

### State
- `accumulator_file`: Running result (starts as "0")
- `multiplicand_file`: The number being multiplied (read-only, read multiple times)
- `work_directory`: For temporary intermediate files

### Operations

#### Operation 1: DOUBLE

**Purpose:** Multiply accumulator by 2 (shift left by 1 bit)

**Implementation:**
```
Open accumulator_file in APPEND mode
Write single byte: '0'
Close file
```

**Effect:** Appends one '0' to the right end of the number

**Example:**
- Before: `1011` (11 in decimal)
- After: `10110` (22 in decimal)

**Memory used:** 1 byte (the '0' being written)

---

#### Operation 2: ADD

**Purpose:** Add multiplicand to accumulator

**Implementation:**

```rust
// Get file lengths (to know where each number ends)
acc_length = get_file_size(accumulator_file)
mcand_length = get_file_size(multiplicand_file)
max_length = max(acc_length, mcand_length)

carry = 0

// Process RIGHT-TO-LEFT (LSB first)
FOR position FROM 0 TO max_length-1:
    // Read accumulator digit at position from right
    IF position < acc_length:
        acc_digit = read_byte_at(accumulator_file, acc_length - 1 - position)
        acc_digit = convert_ascii_to_numeric(acc_digit)  // '0'→0, '1'→1
    ELSE:
        acc_digit = 0  // Pad with zeros

    // Read multiplicand digit at position from right
    IF position < mcand_length:
        mcand_digit = read_byte_at(multiplicand_file, mcand_length - 1 - position)
        mcand_digit = convert_ascii_to_numeric(mcand_digit)
    ELSE:
        mcand_digit = 0

    // Binary addition with carry
    sum = acc_digit + mcand_digit + carry
    result_digit = sum % 2
    carry = sum / 2

    // Store result digit (building result backwards)
    result_buffer[position] = result_digit

// Handle final carry
IF carry > 0:
    result_buffer.append(carry)

// Reverse result buffer (we built it backwards)
reverse(result_buffer)

// Write result to temp file
write(temp_file, result_buffer)

// Replace accumulator with result
delete(accumulator_file)
rename(temp_file, accumulator_file)
```

**Example:**
```
Accumulator:  10110 (22 decimal)
Multiplicand:  1011 (11 decimal)

Position 0 (rightmost):
  acc[4] = 0, mcand[3] = 1, carry = 0
  sum = 0 + 1 + 0 = 1
  result[0] = 1, carry = 0

Position 1:
  acc[3] = 1, mcand[2] = 1, carry = 0
  sum = 1 + 1 + 0 = 2
  result[1] = 0, carry = 1

Position 2:
  acc[2] = 1, mcand[1] = 0, carry = 1
  sum = 1 + 0 + 1 = 2
  result[2] = 0, carry = 1

Position 3:
  acc[1] = 0, mcand[0] = 1, carry = 1
  sum = 0 + 1 + 1 = 2
  result[3] = 0, carry = 1

Position 4:
  acc[0] = 1, mcand = 0 (padded), carry = 1
  sum = 1 + 0 + 1 = 2
  result[4] = 0, carry = 1

Final carry:
  result[5] = 1

Result (reversed): 100001 (33 decimal) ✓
```

**Memory used:**
- 2 single-byte read buffers (for current digits)
- 1 carry byte
- Result buffer: size = max_length + 1
- **Total: O(max_length) for result buffer**

Execute ADD instruction: add multiplicand to accumulator:
Reads both files right-to-left (LSB first)
Writes result LEFT-TO-RIGHT by writing to temp file, then reversing temp to final
Uses only constant memory - no complete number ever loaded.
---

## Complete Multiplication Example

**Problem:** `1011` × `101` = ?

**Step-by-step:**

### Phase 1: Generate Instructions

Read multiplier `101`:
- Bit 0: '1' → `ADD`
- Bit 1: '0' → `DOUBLE`
- Bit 2: '1' → `DOUBLE, ADD`

**Instructions:** `[ADD, DOUBLE, DOUBLE, ADD]`

### Phase 2: Execute Instructions

**Initial state:**
- Accumulator: `0`
- Multiplicand: `1011`

**Execute ADD:**
```
Accumulator: 0
+ Multiplicand: 1011
= Accumulator: 1011
```

**Execute DOUBLE:**
```
Accumulator: 1011
× 2 (append '0')
= Accumulator: 10110
```

**Execute DOUBLE:**
```
Accumulator: 10110
× 2 (append '0')
= Accumulator: 101100
```

**Execute ADD:**
```
Accumulator: 101100
+ Multiplicand: 1011
= Accumulator: 110111
```

**Final result:** `110111` (55 in decimal) ✓

---

## Memory Characteristics

### Constant Memory Operations
- Reading single bits from multiplier
- DOUBLE operation (append '0')
- File length queries

### Linear Memory Operations
- ADD operation: requires buffer of size = result length
- For numbers with N digits, ADD uses O(N) memory

### Total Memory Usage
- **Maximum:** O(N) where N is the length of the larger operand
- **Never loads complete numbers into fixed-size integer types**
- Works for numbers of arbitrary size (limited only by disk space)

---

## Why This Works for Large Numbers

### Example: Multiplying 2^10000 × 2^5000

**File sizes:**
- `multiplicand_file`: 10,001 bytes (the digit '1' followed by 10,000 '0's)
- `multiplier_file`: 5,001 bytes

**Instruction generation:**
- Reads 5,001 bytes sequentially
- Emits 1 ADD + 5000 DOUBLE instructions
- Memory: ~8KB buffer

**Instruction execution:**
- First ADD: reads multiplicand, copies to accumulator
  - Memory: ~10KB buffer for result
- Each DOUBLE: appends single '0'
  - Memory: 1 byte write
- Final result: 15,001 bytes

**Peak memory usage:** ~10-20KB (for buffers during ADD)

**NOT in memory:** Any 15,001-digit integer as a single value

---

## Files Generated During Multiplication

For multiplication of `a.bin × b.bin = result.bin`:

```
work/
├── instructions.bin          (instruction tape from Phase 1)
├── accumulator.bin           (running result, updated after each operation)
└── temp_add_result.bin       (temporary during ADD operations)
```

All files remain on disk for audit and inspection.

---

## Algorithm Complexity

### Time Complexity
- **Instruction generation:** O(M) where M = multiplier length
- **Execution:**
  - M DOUBLE operations: O(M) total (each appends 1 byte)
  - ~M/2 ADD operations (average): O(N × M/2) where N = multiplicand length
  - **Total: O(N × M)**

### Space Complexity
- **Disk:** O(N + M) for inputs, O(N + M) for result
- **Memory:** O(max(N, M)) for addition buffer
- **Never:** O(N × M) or loading numbers into fixed integer types

### Comparison to Standard Multiplication
- Standard bignum libraries (GMP, num-bigint): Load numbers into heap arrays
- This implementation: Processes digit-by-digit from files
- Trade-off: Slower (more disk I/O) but works with extremely constrained memory

---

## Verification Strategy

### Powers of 2 Test
- Input: `2^N` (1 followed by N zeros)
- Verification: Count that result has exactly one '1' and exactly N zeros

### Alternating Pattern Test
- Input: `101010...` (N repetitions) × `11`
- Expected: N×2 ones followed by one zero
- Verification: Stream through file checking each digit without counting

Both tests work without loading complete numbers into memory.

---

## Summary

This multiplication algorithm achieves true **tape-machine** operation:
1. Never loads complete numbers into memory variables
2. Processes files digit-by-digit or in small chunks
3. Works for arbitrarily large numbers (limited by disk, not RAM)
4. All intermediate files visible for audit
5. Constant or linear memory usage, never quadratic

The implementation demonstrates that arithmetic on arbitrarily large numbers can be performed procedurally, similar to a Turing machine operating on an unbounded tape.
 */

use std::fs::{File, OpenOptions};
use std::io::{BufReader, BufWriter, Error, ErrorKind, Read, Result, Seek, SeekFrom, Write};
use std::path::Path;

/// Instruction opcodes for multiplication
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum MultiplyOp {
    /// Double the accumulator (shift left by 1)
    Double = 0,
    /// Add multiplicand to accumulator
    Add = 1,
}

/// Generate instruction tape from multiplier file
///
/// Reads multiplier left-to-right (MSB first)
/// For each bit: emit DOUBLE, then ADD if bit=1
///
/// # Arguments
/// * `multiplier_file` - Binary digits stored MSB-first (left to right)
/// * `instruction_file` - Output file for instruction sequence
///
/// # Errors
/// Returns error if file I/O fails or invalid bit encountered
///
/// # Example
/// Input multiplier: "101" (5 in decimal)
/// Output instructions: [ADD, DOUBLE, DOUBLE, ADD]
fn generate_multiply_instructions(multiplier_file: &Path, instruction_file: &Path) -> Result<()> {
    let mut reader = BufReader::new(File::open(multiplier_file)?);
    let mut writer = BufWriter::new(File::create(instruction_file)?);

    let mut byte_buffer = [0u8; 1];
    let mut first_bit = true;

    // Read multiplier left to right
    loop {
        let bytes_read = reader.read(&mut byte_buffer)?;
        if bytes_read == 0 {
            break;
        }

        let bit = byte_buffer[0];

        // Validate bit is 0 or 1 (defensive)
        if bit != b'0' && bit != b'1' {
            return Err(Error::new(
                ErrorKind::InvalidData,
                format!("Invalid bit value: {}", bit),
            ));
        }

        let is_one = bit == b'1';

        // For first bit: if 1, just ADD (acc=0, so 0+mcand=mcand)
        if first_bit {
            if is_one {
                writer.write_all(&[MultiplyOp::Add as u8])?;
            }
            first_bit = false;
        } else {
            // For subsequent bits: always DOUBLE first, then ADD if bit=1
            writer.write_all(&[MultiplyOp::Double as u8])?;
            if is_one {
                writer.write_all(&[MultiplyOp::Add as u8])?;
            }
        }
    }

    writer.flush()?;
    Ok(())
}

/// Execute DOUBLE instruction: shift accumulator left by 1
///
/// Appends one '0' bit to the right (LSB side)
/// Accumulator stored MSB-first (left to right in file)
///
/// # Arguments
/// * `accumulator_file` - Current accumulator value (modified in place)
///
/// # Errors
/// Returns error if file I/O fails
///
/// # Memory
/// Uses only single-byte buffer
fn execute_double_instruction(accumulator_file: &Path) -> Result<()> {
    // Shift left = append zero to right (in MSB-first storage)
    let mut file = OpenOptions::new().append(true).open(accumulator_file)?;

    file.write_all(&[b'0'])?;
    file.flush()?;

    Ok(())
}

/// Execute ADD instruction: add multiplicand to accumulator
///
/// Reads both files right-to-left (LSB first)
/// Writes result LEFT-TO-RIGHT by writing to temp file, then reversing temp to final
/// Uses only constant memory - no complete number ever loaded
///
/// # Arguments
/// * `accumulator_file` - Current sum (replaced with result)
/// * `multiplicand_file` - Value to add (unchanged)
/// * `work_dir` - Directory for temporary files
///
/// # Errors
/// Returns error if file I/O fails or seek operations fail
///
/// # Memory
/// State: 2 digit buffers + 1 carry byte = 3 bytes (CONSTANT)
fn execute_add_instruction(
    accumulator_file: &Path,
    multiplicand_file: &Path,
    work_dir: &Path,
) -> Result<()> {
    // Get file lengths (to know where LSB is)
    let acc_len = File::open(accumulator_file)?.metadata()?.len() as usize;
    let mcand_len = File::open(multiplicand_file)?.metadata()?.len() as usize;
    let max_len = acc_len.max(mcand_len);

    // Defensive: check for reasonable bounds
    if max_len > 1_000_000_000 {
        return Err(Error::new(
            ErrorKind::InvalidInput,
            "File size exceeds safety limit",
        ));
    }

    // Temporary file for result (written backwards - LSB first)
    let temp_backwards = work_dir.join("temp_add_backwards.bin");
    let mut backwards_writer = BufWriter::new(File::create(&temp_backwards)?);

    let mut acc_file = File::open(accumulator_file)?;
    let mut mcand_file = File::open(multiplicand_file)?;

    let mut carry: u8 = 0;

    // Process right-to-left (LSB first), write result backwards
    for position in 0..max_len {
        // Read accumulator digit at this position (from right)
        let acc_digit = if position < acc_len {
            let acc_idx = acc_len - 1 - position;
            acc_file.seek(SeekFrom::Start(acc_idx as u64))?;
            let mut byte = [0u8; 1];
            acc_file.read_exact(&mut byte)?;

            // Convert ASCII '0'/'1' to numeric 0/1
            if byte[0] == b'0' {
                0u8
            } else if byte[0] == b'1' {
                1u8
            } else {
                return Err(Error::new(
                    ErrorKind::InvalidData,
                    format!("Invalid accumulator digit: {}", byte[0]),
                ));
            }
        } else {
            0u8 // Pad with zeros if accumulator is shorter
        };

        // Read multiplicand digit at this position (from right)
        let mcand_digit = if position < mcand_len {
            let mcand_idx = mcand_len - 1 - position;
            mcand_file.seek(SeekFrom::Start(mcand_idx as u64))?;
            let mut byte = [0u8; 1];
            mcand_file.read_exact(&mut byte)?;

            if byte[0] == b'0' {
                0u8
            } else if byte[0] == b'1' {
                1u8
            } else {
                return Err(Error::new(
                    ErrorKind::InvalidData,
                    format!("Invalid multiplicand digit: {}", byte[0]),
                ));
            }
        } else {
            0u8 // Pad with zeros if multiplicand is shorter
        };

        // Add with carry
        let sum = acc_digit + mcand_digit + carry;
        let result_digit = sum % 2;
        carry = sum / 2;

        // Write digit to backwards file (LSB first)
        backwards_writer.write_all(&[if result_digit == 0 { b'0' } else { b'1' }])?;
    }

    // Handle final carry
    if carry > 0 {
        backwards_writer.write_all(&[b'1'])?;
    }

    backwards_writer.flush()?;
    drop(backwards_writer);

    // Now reverse the backwards file to create the final result
    // Read backwards file from END to START, write to result file
    let temp_result = work_dir.join("temp_add_result.bin");
    reverse_file(&temp_backwards, &temp_result)?;

    // Replace accumulator with result
    std::fs::remove_file(accumulator_file)?;
    std::fs::rename(&temp_result, accumulator_file)?;

    // Cleanup backwards temp file
    let _ = std::fs::remove_file(&temp_backwards);

    Ok(())
}

/// Reverse a file without loading it into memory
///
/// Reads input file from end to start, writes to output file from start to end
/// Uses only single-byte buffer
///
/// # Arguments
/// * `input_file` - File to reverse
/// * `output_file` - Reversed output
///
/// # Memory
/// Uses exactly 1 byte of memory for the current character
fn reverse_file(input_file: &Path, output_file: &Path) -> Result<()> {
    let input_len = File::open(input_file)?.metadata()?.len();

    if input_len == 0 {
        // Empty file - just create empty output
        File::create(output_file)?;
        return Ok(());
    }

    let mut reader = File::open(input_file)?;
    let mut writer = BufWriter::new(File::create(output_file)?);

    // Read from end to start (position counts down)
    for position in (0..input_len).rev() {
        reader.seek(SeekFrom::Start(position))?;

        let mut byte = [0u8; 1];
        reader.read_exact(&mut byte)?;

        // Write to output (sequential)
        writer.write_all(&byte)?;
    }

    writer.flush()?;
    Ok(())
}

/// Multiply two binary numbers using instruction tape
///
/// Algorithm:
/// 1. Generate instruction sequence from multiplier
/// 2. Initialize accumulator to 0
/// 3. Execute each instruction sequentially
///
/// # Arguments
/// * `multiplicand_file` - First operand (read multiple times)
/// * `multiplier_file` - Second operand (read once to generate instructions)
/// * `result_file` - Output file for product
///
/// # Errors
/// Returns error if any file operation fails
///
/// # Example
/// multiplicand_file: "1011" (11 decimal)
/// multiplier_file: "101" (5 decimal)
/// result_file: "110111" (55 decimal)
///
/// # Memory Usage
/// Constant memory - only instruction byte + digit buffers + carry
///
/// # Edge Cases
/// - Multiplying by zero produces zero
/// - Single-bit numbers work correctly
/// - Large numbers (2^1000+) work within disk space limits
pub fn multiply_binary_files(
    multiplicand_file: &Path,
    multiplier_file: &Path,
    result_file: &Path,
) -> Result<()> {
    // Create visible working directory next to result file
    // All intermediate files will be here for inspection
    let work_dir = result_file
        .parent()
        .ok_or_else(|| {
            Error::new(
                ErrorKind::InvalidInput,
                "Result file has no parent directory",
            )
        })?
        .join("work");

    std::fs::create_dir_all(&work_dir)?;

    // Generate instruction tape (visible for inspection)
    let instruction_file = work_dir.join("instructions.bin");
    generate_multiply_instructions(multiplier_file, &instruction_file)?;

    // Initialize accumulator to zero (visible for inspection)
    let accumulator_file = work_dir.join("accumulator.bin");
    File::create(&accumulator_file)?.write_all(&[b'0'])?;

    // Execute instructions sequentially
    let mut instruction_reader = BufReader::new(File::open(&instruction_file)?);
    let mut instruction_byte = [0u8; 1];

    loop {
        let bytes_read = instruction_reader.read(&mut instruction_byte)?;
        if bytes_read == 0 {
            break;
        }

        let opcode = instruction_byte[0];

        if opcode == MultiplyOp::Double as u8 {
            execute_double_instruction(&accumulator_file)?;
        } else if opcode == MultiplyOp::Add as u8 {
            execute_add_instruction(&accumulator_file, multiplicand_file, &work_dir)?;
        } else {
            return Err(Error::new(
                ErrorKind::InvalidData,
                format!("Invalid instruction opcode: {}", opcode),
            ));
        }
    }

    // Copy final accumulator to result
    std::fs::copy(&accumulator_file, result_file)?;

    // Do NOT cleanup - all files must remain for audit

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    /// Helper: create binary file with given bit string
    fn create_binary_file(path: &Path, bits: &str) -> Result<()> {
        let mut file = File::create(path)?;
        file.write_all(bits.as_bytes())?;
        file.flush()?;
        Ok(())
    }

    /// Helper: read binary file as string
    fn read_binary_file(path: &Path) -> Result<String> {
        let contents = std::fs::read(path)?;
        Ok(String::from_utf8(contents).unwrap_or_default())
    }

    #[test]
    fn test_multiply_small_numbers() -> Result<()> {
        // All test files in visible project directory
        let test_dir = std::path::PathBuf::from("./test_output/test1_small");
        std::fs::create_dir_all(&test_dir)?;

        let multiplicand = test_dir.join("multiplicand.bin");
        let multiplier = test_dir.join("multiplier.bin");
        let result = test_dir.join("result.bin");

        // 1011 (11) × 101 (5) = 110111 (55)
        create_binary_file(&multiplicand, "1011")?;
        create_binary_file(&multiplier, "101")?;

        multiply_binary_files(&multiplicand, &multiplier, &result)?;

        let result_str = read_binary_file(&result)?;
        assert_eq!(result_str, "110111");

        // Do NOT cleanup - files must be inspectable

        Ok(())
    }

    #[test]
    fn test_multiply_by_zero() -> Result<()> {
        let test_dir = std::path::PathBuf::from("./test_output/test2_zero");
        std::fs::create_dir_all(&test_dir)?;

        let multiplicand = test_dir.join("multiplicand.bin");
        let multiplier = test_dir.join("multiplier.bin");
        let result = test_dir.join("result.bin");

        create_binary_file(&multiplicand, "1111")?;
        create_binary_file(&multiplier, "0")?;

        multiply_binary_files(&multiplicand, &multiplier, &result)?;

        let result_str = read_binary_file(&result)?;
        assert_eq!(result_str, "0");

        // Do NOT cleanup - files must be inspectable

        Ok(())
    }

    #[test]
    fn test_multiply_powers_of_two() -> Result<()> {
        let test_dir = std::path::PathBuf::from("./test_output/test3_powers");
        std::fs::create_dir_all(&test_dir)?;

        let multiplicand = test_dir.join("multiplicand.bin");
        let multiplier = test_dir.join("multiplier.bin");
        let result = test_dir.join("result.bin");

        // 100 (4) × 10 (2) = 1000 (8)
        create_binary_file(&multiplicand, "100")?;
        create_binary_file(&multiplier, "10")?;

        multiply_binary_files(&multiplicand, &multiplier, &result)?;

        let result_str = read_binary_file(&result)?;
        assert_eq!(result_str, "1000");

        // Do NOT cleanup - files must be inspectable

        Ok(())
    }
}

/// Read two binary files and multiply them, writing result to third file
///
/// # Arguments
/// * `multiplicand_path` - Path to first input file
/// * `multiplier_path` - Path to second input file
/// * `result_path` - Path to output file
///
/// # Errors
/// Returns error if files don't exist or multiplication fails
///
/// # Example
/// ```
/// multiply_from_files("./data/num_a.bin", "./data/num_b.bin", "./output/product.bin")
/// ```
pub fn multiply_from_files(
    multiplicand_path: &Path,
    multiplier_path: &Path,
    result_path: &Path,
) -> Result<()> {
    // Verify input files exist
    if !multiplicand_path.exists() {
        return Err(Error::new(
            ErrorKind::NotFound,
            format!("Multiplicand file not found: {:?}", multiplicand_path),
        ));
    }

    if !multiplier_path.exists() {
        return Err(Error::new(
            ErrorKind::NotFound,
            format!("Multiplier file not found: {:?}", multiplier_path),
        ));
    }

    println!("Reading multiplicand from: {:?}", multiplicand_path);
    println!("Reading multiplier from: {:?}", multiplier_path);
    println!("Will write result to: {:?}", result_path);

    multiply_binary_files(multiplicand_path, multiplier_path, result_path)?;

    println!("Multiplication complete!");
    Ok(())
}

/// Generate a power-of-2 binary file: "1" followed by N zeros
///
/// # Arguments
/// * `output_path` - Where to write the file
/// * `num_zeros` - How many zeros after the leading 1
///
/// # Example
/// generate_power_of_2("./test.bin", 1000) creates file with "1000...000" (1001 digits)
pub fn generate_power_of_2(output_path: &Path, num_zeros: usize) -> Result<()> {
    let mut file = BufWriter::new(File::create(output_path)?);

    // Write leading '1'
    file.write_all(&[b'1'])?;

    // Write zeros in chunks (efficient for large numbers)
    const CHUNK_SIZE: usize = 8192;
    let zero_chunk = vec![b'0'; CHUNK_SIZE];

    let full_chunks = num_zeros / CHUNK_SIZE;
    let remainder = num_zeros % CHUNK_SIZE;

    // Write full chunks
    for _ in 0..full_chunks {
        file.write_all(&zero_chunk)?;
    }

    // Write remaining zeros
    if remainder > 0 {
        file.write_all(&zero_chunk[..remainder])?;
    }

    file.flush()?;
    Ok(())
}

/// Verify that a binary file is a power of 2 (one '1' followed by N '0's)
///
/// # Arguments
/// * `file_path` - File to verify
/// * `expected_zeros` - Expected number of zeros after the '1'
///
/// # Returns
/// Ok(()) if valid, Error if not
pub fn verify_power_of_2(file_path: &Path, expected_zeros: usize) -> Result<()> {
    let mut reader = BufReader::new(File::open(file_path)?);
    let mut byte = [0u8; 1];

    // Check first byte is '1'
    reader.read_exact(&mut byte)?;
    if byte[0] != b'1' {
        return Err(Error::new(
            ErrorKind::InvalidData,
            format!("First digit is '{}', expected '1'", byte[0] as char),
        ));
    }

    // Count zeros
    let mut zero_count = 0usize;

    loop {
        match reader.read(&mut byte) {
            Ok(0) => break, // EOF
            Ok(_) => {
                if byte[0] == b'0' {
                    zero_count += 1;
                } else {
                    return Err(Error::new(
                        ErrorKind::InvalidData,
                        format!(
                            "Found non-zero digit '{}' at position {}",
                            byte[0] as char,
                            zero_count + 1
                        ),
                    ));
                }
            }
            Err(e) => return Err(e),
        }
    }

    // Verify zero count
    if zero_count != expected_zeros {
        return Err(Error::new(
            ErrorKind::InvalidData,
            format!("Found {} zeros, expected {}", zero_count, expected_zeros),
        ));
    }

    println!("✓ Verified: 1 followed by {} zeros", zero_count);
    Ok(())
}

#[cfg(test)]
mod large_tests {
    use super::*;

    #[test]
    fn test_multiply_large_powers_of_2() -> Result<()> {
        let test_dir = std::path::PathBuf::from("./test_output/test4_large");
        std::fs::create_dir_all(&test_dir)?;

        let a_path = test_dir.join("power_2_to_1000.bin");
        let b_path = test_dir.join("power_2_to_500.bin");
        let result_path = test_dir.join("result.bin");

        // Generate 2^1000 (1 followed by 1000 zeros)
        println!("Generating 2^1000...");
        generate_power_of_2(&a_path, 1000)?;

        // Generate 2^500 (1 followed by 500 zeros)
        println!("Generating 2^500...");
        generate_power_of_2(&b_path, 500)?;

        // Multiply: 2^1000 × 2^500 = 2^1500
        println!("Multiplying 2^1000 × 2^500...");
        multiply_from_files(&a_path, &b_path, &result_path)?;

        // Verify result is 2^1500 (1 followed by 1500 zeros)
        println!("Verifying result is 2^1500...");
        verify_power_of_2(&result_path, 1500)?;

        println!("✓ Large multiplication test passed!");

        Ok(())
    }

    #[test]
    fn test_multiply_very_large_powers_of_2() -> Result<()> {
        let test_dir = std::path::PathBuf::from("./test_output/test5_very_large");
        std::fs::create_dir_all(&test_dir)?;

        let a_path = test_dir.join("power_2_to_10000.bin");
        let b_path = test_dir.join("power_2_to_5000.bin");
        let result_path = test_dir.join("result.bin");

        // Generate 2^10000
        println!("Generating 2^10000 (10,001 digits)...");
        generate_power_of_2(&a_path, 10_000)?;

        // Generate 2^5000
        println!("Generating 2^5000 (5,001 digits)...");
        generate_power_of_2(&b_path, 5_000)?;

        // Multiply: 2^10000 × 2^5000 = 2^15000
        println!("Multiplying 2^10000 × 2^5000...");
        multiply_from_files(&a_path, &b_path, &result_path)?;

        // Verify result is 2^15000
        println!("Verifying result is 2^15000 (15,001 digits)...");
        verify_power_of_2(&result_path, 15_000)?;

        println!("✓ Very large multiplication test passed!");

        Ok(())
    }
}

/// Generate pattern "10" repeated N times
///
/// # Arguments
/// * `output_path` - Where to write the file
/// * `n_repetitions` - Number of times to repeat "10"
///
/// # Example
/// generate_alternating_10_pattern("./test.bin", 4) creates "10101010"
pub fn generate_alternating_10_pattern(output_path: &Path, n_repetitions: usize) -> Result<()> {
    let mut file = BufWriter::new(File::create(output_path)?);

    // Write "10" repeated N times in chunks
    const CHUNK_SIZE: usize = 4096; // Must be even for "10" pattern
    let pattern_chunk = vec![b'1', b'0'].repeat(CHUNK_SIZE / 2);

    let full_chunks = (n_repetitions * 2) / CHUNK_SIZE;
    let remainder = (n_repetitions * 2) % CHUNK_SIZE;

    // Write full chunks
    for _ in 0..full_chunks {
        file.write_all(&pattern_chunk)?;
    }

    // Write remaining bytes
    if remainder > 0 {
        file.write_all(&pattern_chunk[..remainder])?;
    }

    file.flush()?;
    Ok(())
}

/// Generate binary "11"
///
/// # Arguments
/// * `output_path` - Where to write the file
pub fn generate_eleven(output_path: &Path) -> Result<()> {
    let mut file = File::create(output_path)?;
    file.write_all(b"11")?;
    file.flush()?;
    Ok(())
}
/// Verify pattern: "10" repeated N times multiplied by "11"
/// Expected result: all '1's followed by one '0'
/// Length should be 2N+1
///
/// # Arguments
/// * `result_path` - File to verify
/// * `n_repetitions` - N from input pattern (10 repeated N times)
///
/// # Returns
/// Ok(()) if pattern matches, Error if not
///
/// # Example
/// Input: 10101010 (N=4, 8 digits)
/// Output: 111111110 (9 digits: 8 ones, then 1 zero)
pub fn verify_alternating_pattern_times_eleven(
    result_path: &Path,
    n_repetitions: usize,
) -> Result<()> {
    let mut reader = BufReader::new(File::open(result_path)?);
    let mut byte = [0u8; 1];

    let input_length = 2 * n_repetitions;
    let expected_result_length = input_length + 1;
    let expected_ones = input_length; // All digits except last should be '1'

    println!("Verifying pattern for N={}:", n_repetitions);
    println!("  Input length: {} digits", input_length);
    println!(
        "  Expected result length: {} digits",
        expected_result_length
    );
    println!("  Expected: {} ones, then 1 zero", expected_ones);

    // Count ones from the start
    let mut ones_count = 0usize;

    loop {
        match reader.read(&mut byte) {
            Ok(0) => {
                // Reached EOF - should not happen before we find the final zero
                return Err(Error::new(
                    ErrorKind::InvalidData,
                    format!(
                        "Unexpected EOF after {} ones (expected {} ones + 1 zero)",
                        ones_count, expected_ones
                    ),
                ));
            }
            Ok(_) => {
                if byte[0] == b'1' {
                    ones_count += 1;

                    // Check we haven't exceeded expected ones
                    if ones_count > expected_ones {
                        return Err(Error::new(
                            ErrorKind::InvalidData,
                            format!("Found more than {} ones", expected_ones),
                        ));
                    }
                } else if byte[0] == b'0' {
                    // Found the zero - should be at the end
                    break;
                } else {
                    return Err(Error::new(
                        ErrorKind::InvalidData,
                        format!(
                            "Found unexpected digit '{}' at position {}",
                            byte[0] as char,
                            ones_count + 1
                        ),
                    ));
                }
            }
            Err(e) => return Err(e),
        }
    }

    // Verify we found exactly the right number of ones before the zero
    if ones_count != expected_ones {
        return Err(Error::new(
            ErrorKind::InvalidData,
            format!(
                "Found {} ones before final zero, expected {}",
                ones_count, expected_ones
            ),
        ));
    }
    println!("  ✓ Found {} ones", ones_count);
    println!("  ✓ Found final '0'");

    // Verify nothing after the final zero
    match reader.read(&mut byte) {
        Ok(0) => {
            println!(
                "  ✓ Total length is {} (as expected)",
                expected_result_length
            );
        }
        Ok(_) => {
            return Err(Error::new(
                ErrorKind::InvalidData,
                format!(
                    "Found unexpected digit '{}' after final zero",
                    byte[0] as char
                ),
            ));
        }
        Err(e) => return Err(e),
    }

    println!("✓ Pattern verification passed!");
    Ok(())
}
#[cfg(test)]
mod pattern_tests {
    use super::*;

    #[test]
    fn test_alternating_pattern_small() -> Result<()> {
        let test_dir = std::path::PathBuf::from("./test_output/test6_pattern_small");
        std::fs::create_dir_all(&test_dir)?;

        let n = 4; // "10101010" (8 digits)

        let a_path = test_dir.join("pattern_10_times_4.bin");
        let b_path = test_dir.join("eleven.bin");
        let result_path = test_dir.join("result.bin");

        // Generate "10101010"
        println!("Generating '10' repeated {} times...", n);
        generate_alternating_10_pattern(&a_path, n)?;

        // Generate "11"
        generate_eleven(&b_path)?;

        // Multiply
        println!("Multiplying pattern × 11...");
        multiply_from_files(&a_path, &b_path, &result_path)?;

        // Verify: should be "0111111110"
        verify_alternating_pattern_times_eleven(&result_path, n)?;

        Ok(())
    }

    #[test]
    fn test_alternating_pattern_medium() -> Result<()> {
        let test_dir = std::path::PathBuf::from("./test_output/test7_pattern_medium");
        std::fs::create_dir_all(&test_dir)?;

        let n = 1000; // 2000 digits input

        let a_path = test_dir.join("pattern_10_times_1000.bin");
        let b_path = test_dir.join("eleven.bin");
        let result_path = test_dir.join("result.bin");

        println!("Generating '10' repeated {} times ({} digits)...", n, n * 2);
        generate_alternating_10_pattern(&a_path, n)?;

        generate_eleven(&b_path)?;

        println!("Multiplying pattern × 11...");
        multiply_from_files(&a_path, &b_path, &result_path)?;

        // Verify: 0 + (2000 ones) + 0
        verify_alternating_pattern_times_eleven(&result_path, n)?;

        Ok(())
    }

    #[test]
    fn test_alternating_pattern_large() -> Result<()> {
        let test_dir = std::path::PathBuf::from("./test_output/test8_pattern_large");
        std::fs::create_dir_all(&test_dir)?;

        let n = 10_000; // 20,000 digits input

        let a_path = test_dir.join("pattern_10_times_10000.bin");
        let b_path = test_dir.join("eleven.bin");
        let result_path = test_dir.join("result.bin");

        println!("Generating '10' repeated {} times ({} digits)...", n, n * 2);
        generate_alternating_10_pattern(&a_path, n)?;

        generate_eleven(&b_path)?;

        println!("Multiplying pattern × 11...");
        multiply_from_files(&a_path, &b_path, &result_path)?;

        // Verify: 0 + (20,000 ones) + 0
        verify_alternating_pattern_times_eleven(&result_path, n)?;

        Ok(())
    }
}

fn main() -> Result<()> {
    println!("Binary Multiplication - Tape Machine Implementation");
    println!("====================================================\n");

    let demo_dir = std::path::PathBuf::from("./demo_output");
    std::fs::create_dir_all(&demo_dir)?;

    let multiplicand = demo_dir.join("multiplicand.bin");
    let multiplier = demo_dir.join("multiplier.bin");
    let result = demo_dir.join("result.bin");

    // Demo: 1011 (11) × 101 (5) = 110111 (55)
    File::create(&multiplicand)?.write_all(b"1011")?;
    File::create(&multiplier)?.write_all(b"101")?;

    println!("Multiplicand: 1011 (11 decimal)");
    println!("Multiplier:   101 (5 decimal)");
    println!("\nExecuting multiplication...\n");

    multiply_binary_files(&multiplicand, &multiplier, &result)?;

    let result_str = std::fs::read_to_string(&result)?;
    println!("Result: {} (55 decimal)", result_str);
    println!("\nAll files saved to: {:?}", demo_dir);
    println!("Inspect: multiplicand.bin, multiplier.bin, result.bin");
    println!("Working files in: {:?}", demo_dir.join("work"));

    Ok(())
}
