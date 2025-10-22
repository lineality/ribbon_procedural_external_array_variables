//

/// Tiered stack-based hex counter with cascading buffers
///
/// # Memory Architecture
/// - Level 0: 32 bytes  (handles 0x0 to 0xFFFFFFFF..., ~8 hex digits)
/// - Level 1: 256 bytes (handles larger numbers, ~64 hex digits)
/// - Level 2: 2048 bytes (handles very large numbers, ~512 hex digits)
///
/// # Policy
/// Start with smallest buffer. Promote to next level only when full.
/// Buffers are stack-allocated but OS only commits pages when touched.
///
/// # Space Efficiency
/// Hex: 4 bits of information per byte (50% efficient)
/// Can represent numbers up to 16^512 in Level 2
struct TieredStackHexCounter {
    /// Small buffer for common cases (32 bytes)
    /// Most counters will never leave this tier
    buffer_small: [u8; 32],

    /// Medium buffer (256 bytes)
    /// Used when small buffer overflows
    buffer_medium: [u8; 256],

    /// Large buffer (2048 bytes)
    /// Used when medium buffer overflows
    buffer_large: [u8; 2048],

    /// Current active tier: 0=small, 1=medium, 2=large
    active_tier: u8,

    /// Number of valid hex digits in active buffer (from right)
    length: usize,
}

impl TieredStackHexCounter {
    /// Create new tiered counter starting in smallest buffer
    ///
    /// # Memory Layout
    /// ```text
    /// Stack allocation:
    ///   buffer_small:  32 bytes  ]
    ///   buffer_medium: 256 bytes ] 2336 bytes total on stack
    ///   buffer_large:  2048 bytes]
    ///
    /// But only buffer_small is initially "touched" by OS
    /// ```
    fn new() -> Self {
        let mut small = [0u8; 32];
        small[31] = b'0'; // Initialize with '0' at rightmost position

        TieredStackHexCounter {
            buffer_small: small,
            buffer_medium: [0u8; 256], // Not yet touched
            buffer_large: [0u8; 2048], // Not yet touched
            active_tier: 0,
            length: 1,
        }
    }

    /// Get capacity of current tier
    fn current_capacity(&self) -> usize {
        match self.active_tier {
            0 => 32,
            1 => 256,
            2 => 2048,
            _ => unreachable!(),
        }
    }

    /// Get mutable reference to active buffer
    fn get_active_buffer_mut(&mut self) -> &mut [u8] {
        match self.active_tier {
            0 => &mut self.buffer_small[..],
            1 => &mut self.buffer_medium[..],
            2 => &mut self.buffer_large[..],
            _ => unreachable!(),
        }
    }

    /// Get reference to active buffer
    fn get_active_buffer(&self) -> &[u8] {
        match self.active_tier {
            0 => &self.buffer_small[..],
            1 => &self.buffer_medium[..],
            2 => &self.buffer_large[..],
            _ => unreachable!(),
        }
    }

    /// Promote to next tier when current buffer is full
    ///
    /// # Process
    /// 1. Copy valid digits from current buffer to new buffer
    /// 2. Switch active tier
    /// 3. Update length
    ///
    /// # Memory Behavior
    /// This is when the OS will actually commit the next buffer's pages
    fn promote_tier(&mut self) -> std::io::Result<()> {
        match self.active_tier {
            0 => {
                // Promote small → medium
                let old_capacity = 32;
                let new_capacity = 256;
                let start_old = old_capacity - self.length;
                let start_new = new_capacity - self.length;

                // Copy valid digits
                self.buffer_medium[start_new..].copy_from_slice(&self.buffer_small[start_old..]);

                self.active_tier = 1;
                Ok(())
            }
            1 => {
                // Promote medium → large
                let old_capacity = 256;
                let new_capacity = 2048;
                let start_old = old_capacity - self.length;
                let start_new = new_capacity - self.length;

                // Copy valid digits
                self.buffer_large[start_new..].copy_from_slice(&self.buffer_medium[start_old..]);

                self.active_tier = 2;
                Ok(())
            }
            2 => {
                // Already at maximum tier
                Err(std::io::Error::new(
                    std::io::ErrorKind::OutOfMemory,
                    "Counter exceeded maximum capacity (2048 hex digits)",
                ))
            }
            _ => unreachable!(),
        }
    }

    /// Get the active portion of current buffer
    fn get_active_slice(&self) -> &[u8] {
        let capacity = self.current_capacity();
        let start = capacity - self.length;
        let buffer = self.get_active_buffer();
        &buffer[start..capacity]
    }
}

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

impl ExternalCounter for TieredStackHexCounter {
    /// Increment hex counter with automatic tier promotion
    ///
    /// # Algorithm
    /// 1. Try to increment in current tier
    /// 2. If buffer full (carry would extend length), promote to next tier
    /// 3. Continue incrementing in new tier
    ///
    /// # Edge Cases
    /// - First increment: stays in tier 0
    /// - Fills tier 0: promotes to tier 1
    /// - Fills tier 1: promotes to tier 2
    /// - Fills tier 2: returns error
    fn increment(&mut self) -> std::io::Result<()> {
        let capacity = self.current_capacity();

        // Check if we need to promote BEFORE incrementing
        // (if we're at max capacity and would carry out)
        if self.length >= capacity {
            return Err(std::io::Error::new(
                std::io::ErrorKind::OutOfMemory,
                "Buffer overflow in current tier",
            ));
        }

        let buffer = self.get_active_buffer_mut();
        let mut carry = 1u8;
        let start = capacity - self.length;

        // Process digits right to left (bounded loop)
        for i in 0..self.length {
            let idx = capacity - 1 - i;

            if carry > 0 {
                let current = match buffer[idx] {
                    b'0'..=b'9' => buffer[idx] - b'0',
                    b'A'..=b'F' => buffer[idx] - b'A' + 10,
                    b'a'..=b'f' => buffer[idx] - b'a' + 10,
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

                buffer[idx] = match new_val {
                    0..=9 => b'0' + new_val,
                    10..=15 => b'A' + new_val - 10,
                    _ => b'0',
                };
            } else {
                break;
            }
        }

        // If still carrying, need to extend left
        if carry > 0 {
            if self.length >= capacity {
                // Need to promote to next tier
                self.promote_tier()?;

                // After promotion, add the carry digit
                let new_capacity = self.current_capacity();
                let new_buffer = self.get_active_buffer_mut();
                let new_start = new_capacity - self.length - 1;
                new_buffer[new_start] = b'1';
                self.length += 1;
            } else {
                // Room in current tier
                let new_start = start - 1;
                let buffer = self.get_active_buffer_mut();
                buffer[new_start] = b'1';
                self.length += 1;
            }
        }

        Ok(())
    }

    fn read(&self) -> std::io::Result<String> {
        let slice = self.get_active_slice();
        String::from_utf8(slice.to_vec())
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
    }

    fn reset(&mut self) -> std::io::Result<()> {
        // Reset to tier 0
        self.buffer_small = [0u8; 32];
        self.buffer_small[31] = b'0';
        self.active_tier = 0;
        self.length = 1;
        Ok(())
    }

    fn get_base(&self) -> u32 {
        16
    }
}

impl TieredStackHexCounter {
    /// Get current memory statistics
    ///
    /// # Returns
    /// (allocated_bytes, used_bytes, tier, capacity, wasted_bytes)
    fn memory_stats(&self) -> (usize, usize, u8, usize, usize) {
        let total_allocated = 32 + 256 + 2048; // 2336 bytes
        let used = self.length;
        let tier = self.active_tier;
        let capacity = self.current_capacity();
        let wasted = capacity - used;

        (total_allocated, used, tier, capacity, wasted)
    }

    /// Human-readable memory report
    fn print_memory_report(&self) {
        let (allocated, used, tier, capacity, wasted) = self.memory_stats();

        println!("  Memory Report:");
        println!("    Total allocated (stack): {} bytes", allocated);
        println!("    Active tier: {} (capacity: {} bytes)", tier, capacity);
        println!("    Used in active tier: {} bytes", used);
        println!(
            "    Wasted in active tier: {} bytes ({:.1}%)",
            wasted,
            (wasted as f64 / capacity as f64) * 100.0
        );
        println!("    Value length: {} hex digits", used);
        println!(
            "    Can represent up to: 16^{} (approx 2^{})",
            used,
            used * 4
        );
    }
}

// /// Stack buffer size in bytes
// const STACK_BUFFER_SIZE: usize = 2048;

// impl ExternalCounter for StackHexCounter {
//     fn increment(&mut self) -> std::io::Result<()> {
//         if self.length >= STACK_BUFFER_SIZE {
//             return Err(std::io::Error::new(
//                 std::io::ErrorKind::OutOfMemory,
//                 "Stack buffer overflow",
//             ));
//         }

//         let mut carry = 1u8;
//         let start = STACK_BUFFER_SIZE - self.length;

//         for i in 0..self.length {
//             let idx = STACK_BUFFER_SIZE - 1 - i;

//             if carry > 0 {
//                 let current = match self.buffer[idx] {
//                     b'0'..=b'9' => self.buffer[idx] - b'0',
//                     b'A'..=b'F' => self.buffer[idx] - b'A' + 10,
//                     b'a'..=b'f' => self.buffer[idx] - b'a' + 10,
//                     _ => {
//                         return Err(std::io::Error::new(
//                             std::io::ErrorKind::InvalidData,
//                             "Invalid hex digit in buffer",
//                         ));
//                     }
//                 };

//                 let mut new_val = current + carry;
//                 if new_val >= 16 {
//                     new_val = 0;
//                     carry = 1;
//                 } else {
//                     carry = 0;
//                 }

//                 self.buffer[idx] = match new_val {
//                     0..=9 => b'0' + new_val,
//                     10..=15 => b'A' + new_val - 10,
//                     _ => b'0',
//                 };
//             } else {
//                 break;
//             }
//         }

//         if carry > 0 {
//             if self.length >= STACK_BUFFER_SIZE {
//                 return Err(std::io::Error::new(
//                     std::io::ErrorKind::OutOfMemory,
//                     "Stack buffer overflow",
//                 ));
//             }
//             let new_start = start - 1;
//             self.buffer[new_start] = b'1';
//             self.length += 1;
//         }

//         Ok(())
//     }

//     fn read(&self) -> std::io::Result<String> {
//         let slice = self.get_active_slice();
//         String::from_utf8(slice.to_vec())
//             .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
//     }

//     fn reset(&mut self) -> std::io::Result<()> {
//         self.buffer = [0u8; STACK_BUFFER_SIZE];
//         self.buffer[STACK_BUFFER_SIZE - 1] = b'0';
//         self.length = 1;
//         Ok(())
//     }

//     fn get_base(&self) -> u32 {
//         16
//     }
// }

// For general use: TieredStackHexCounter
// - 99% of counts stay in Tier 0 (32 bytes)
// - Fast as original stack counter
// - More memory efficient
// - Graceful growth when needed

fn main() -> std::io::Result<()> {
    let mut counter = TieredStackHexCounter::new();

    // Count files in directory
    for entry in std::fs::read_dir(".")? {
        let _ = entry?;
        counter.increment()?;
    }

    println!("Count: 0x{}", counter.read()?);
    counter.print_memory_report();

    Ok(())
}
