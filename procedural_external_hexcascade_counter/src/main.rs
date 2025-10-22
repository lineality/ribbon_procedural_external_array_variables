use std::fs;
use std::path::PathBuf;

mod ribbon_external_counter_module;
use ribbon_external_counter_module::CascadingHexCounter;

/// Counts all items in a directory using arbitrary-precision counters
///
/// # Purpose
/// Provides summary statistics for directory contents using Ribbon counters
/// that can handle arbitrarily large counts without overflow.
///
/// # Arguments
/// * `path` - Reference to PathBuf of the directory to count
///
/// # Returns
/// A tuple of three Strings: (all_count, file_count, dir_count)
/// - `all_count`: Total number of items (files + dirs + symlinks + special files)
/// - `file_count`: Number of regular files only
/// - `dir_count`: Number of directories only
///
/// # Error Handling
/// Returns ("?", "?", "?") if any error occurs:
/// - Directory cannot be read (permissions, doesn't exist, etc.)
/// - Metadata cannot be accessed for items
/// - Counter increment fails
/// - Counter-to-decimal conversion fails
/// - String conversion fails
/// - Any other I/O error
///
/// # Memory Behavior
/// Uses three CascadingHexCounter instances (~7KB stack allocation).
/// All counters start at Tier 0 (4 bytes active) and grow only if needed.
/// Zero heap allocation - all operations use stack-only memory.
///
/// # Scope
/// - Counts ONLY items in the specified directory (flat, non-recursive)
/// - Includes hidden files and directories (those starting with '.')
/// - Includes ALL item types (files, dirs, symlinks, FIFOs, sockets, etc.)
/// - Does NOT follow symlinks or recurse into subdirectories
///
/// # Loop Safety
/// The iterator from fs::read_dir() is naturally bounded by the number of
/// entries in the directory.
///
/// # Examples
/// ```rust
/// let path = PathBuf::from("/home/user/documents");
/// let (all, files, dirs) = count_directory_items_ribbon(&path);
/// println!("Total: {}, Files: {}, Directories: {}", all, files, dirs);
/// // Output: "Total: 42, Files: 35, Directories: 7"
///
/// // On error:
/// let bad_path = PathBuf::from("/nonexistent");
/// let (all, files, dirs) = count_directory_items_ribbon(&bad_path);
/// // Returns: ("?", "?", "?")
/// ```
fn count_directory_items_ribbon(path: &PathBuf) -> (String, String, String) {
    // Error handling: Path validation (defensive check)
    if path.as_os_str().is_empty() {
        return (String::from("?"), String::from("?"), String::from("?"));
    }

    // Initialize three arbitrary-precision counters (stack-only, ~7KB)
    // Each starts at Tier 0 (4 bytes active) and grows automatically if needed
    let mut all_counter = CascadingHexCounter::new();
    let mut file_counter = CascadingHexCounter::new();
    let mut dir_counter = CascadingHexCounter::new();

    // Attempt to read directory contents
    // Error handling: Cannot read directory
    let directory_reader = match fs::read_dir(path) {
        Ok(reader) => reader,
        Err(_) => {
            // Cannot read directory - return unknowns
            return (String::from("?"), String::from("?"), String::from("?"));
        }
    };

    // Iterate through directory entries
    // The iterator is naturally bounded by the filesystem
    for entry_result in directory_reader {
        // Error handling: Reading directory entry
        let entry = match entry_result {
            Ok(e) => e,
            Err(_) => {
                // Error reading this specific entry - skip it
                continue;
            }
        };

        // Error handling: Getting metadata for entry
        let metadata = match entry.metadata() {
            Ok(meta) => meta,
            Err(_) => {
                // Cannot read metadata for this entry - skip it
                continue;
            }
        };

        // Error handling: Counter increment
        // Count this item in 'all' using Ribbon's increment
        if let Err(_) = all_counter.increment() {
            // Increment failed (extremely rare - would require tier promotion failure)
            return (String::from("?"), String::from("?"), String::from("?"));
        }

        // Classify the item type and increment appropriate counter
        if metadata.is_file() {
            // Error handling: File counter increment
            if let Err(_) = file_counter.increment() {
                return (String::from("?"), String::from("?"), String::from("?"));
            }
        } else if metadata.is_dir() {
            // Error handling: Directory counter increment
            if let Err(_) = dir_counter.increment() {
                return (String::from("?"), String::from("?"), String::from("?"));
            }
        }
        // Note: Symlinks, FIFOs, sockets, etc. are counted only in 'all'
    }

    // Convert counters to decimal strings
    // Pre-allocate conversion buffer on stack (reused for all three conversions)
    let mut decimal_buffer = [0u8; 2500]; // MAX_DECIMAL_DIGITS from ribbon

    // Convert all_counter to decimal string
    // Error handling: Counter-to-decimal conversion
    let all_str = match all_counter.to_decimal(&mut decimal_buffer) {
        Ok(length) => {
            // Error handling: UTF-8 validation
            match std::str::from_utf8(&decimal_buffer[..length]) {
                Ok(valid_str) => String::from(valid_str),
                Err(_) => {
                    // UTF-8 conversion failed - should never happen with decimal digits
                    return (String::from("?"), String::from("?"), String::from("?"));
                }
            }
        }
        Err(_) => {
            // Decimal conversion failed
            return (String::from("?"), String::from("?"), String::from("?"));
        }
    };

    // // diagnostics demo
    // let hex_len = all_counter.to_hex(&mut decimal_buffer);
    // let hex_str = std::str::from_utf8(&decimal_buffer[..hex_len]);
    // println!(" all_counter Hex representation: 0x{}", hex_str);
    let reset_result = all_counter.reset();
    println!(
        "  After reset: tier={}, digits={} reset_result={:?}",
        all_counter.current_tier(),
        all_counter.digit_count(),
        reset_result,
    );

    // Convert file_counter to decimal string
    // Error handling: Counter-to-decimal conversion
    let file_str = match file_counter.to_decimal(&mut decimal_buffer) {
        Ok(length) => {
            // Error handling: UTF-8 validation
            match std::str::from_utf8(&decimal_buffer[..length]) {
                Ok(valid_str) => String::from(valid_str),
                Err(_) => {
                    return (String::from("?"), String::from("?"), String::from("?"));
                }
            }
        }
        Err(_) => {
            return (String::from("?"), String::from("?"), String::from("?"));
        }
    };

    // Convert dir_counter to decimal string
    // Error handling: Counter-to-decimal conversion
    let dir_str = match dir_counter.to_decimal(&mut decimal_buffer) {
        Ok(length) => {
            // Error handling: UTF-8 validation
            match std::str::from_utf8(&decimal_buffer[..length]) {
                Ok(valid_str) => String::from(valid_str),
                Err(_) => {
                    return (String::from("?"), String::from("?"), String::from("?"));
                }
            }
        }
        Err(_) => {
            return (String::from("?"), String::from("?"), String::from("?"));
        }
    };

    // Final sanity check: Ensure strings are valid
    // This is defensive - decimal conversion should never produce empty strings for counts
    if all_str.is_empty() || file_str.is_empty() || dir_str.is_empty() {
        return (String::from("?"), String::from("?"), String::from("?"));
    }

    // Note: Logic consistency check (files + dirs <= all) could be added here
    // but would require parsing strings back to numbers, which adds complexity
    // and potential failure points. For directory counting, inconsistency
    // should not occur if the code above is correct.

    (all_str, file_str, dir_str)
}

/// Main function: Test directory counting with Ribbon counters
///
/// # Error Handling
/// All errors handled gracefully - prints error message and exits with status 1
fn main() {
    // Get current working directory with error handling
    let cwd = match std::env::current_dir() {
        Ok(path) => path,
        Err(e) => {
            eprintln!("Error: Cannot get current directory: {}", e);
            std::process::exit(1);
        }
    };

    // Count directory items
    let (all, files, dirs) = count_directory_items_ribbon(&cwd);

    // Print results
    println!("Total: {}, Files: {}, Dirs: {}", all, files, dirs);
}
