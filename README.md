# ribbon_procedural_external_array_variables

ribbon: Procedural External Array Variables
"It's tape all the way down."

externalized procedural variables implemented in rust

ribbon_procedural_external_array_variables

E.g. count the number of items in a directory (or count the number of time-units past) using an 'externalized' procedural method whereby a representation is incrementally updated:

overall:
- stack decimal test to be quickest
- stack hex tends to be most memory-efficient and 


### Options:
A. on disk
B. in dynamic heap memory
C. compromise: pre-allocated buffer on stack (fixed, but large for a representation. say 2048b).

#### for pre-allocated [u8; 2048] array
For binary: up to 2048 bits of precision (numbers up to 2^2048)
For decimal: up to 2048 digits (numbers up to 10^2048)
For hex: up to 2048 hex digits (numbers up to 16^2048)

such that the current total record, as either binary digits or dynamic array structures, never attempts to 'load' the value into 'memory' as a single 'value,' rather the value is represented by a procedurally generated and modified external representation, e.g. either on physical 'disk' or in dynamic heap-memory, or in pre-allocated memory (which would be less size-flexible). 


One testing goal-set is to compare performance inside usize limits. Another crucial task must be to demonstrate on >usize counting.

If dwelling on analogy, strings are entities that can be handled, but are arrays of smaller subunits. Numbers by custom are fixed into 'whole-loaded' units (short, long, float, unsigned, double,etc.), which makes sense for common small-fast computations. But there should be an option for, if rare, large-slow computations that deal with numbers more like string-arrays, not attempting whole-load logic operations. 

1. Straight counting
2. parallel/concurrent counting


## Disk version:
Create a file (or two files) that house the external representation.
On the first count this file contains a binary 1..

The next time this representation is incremented, it should be possible to incrementally move binary digit by binary digit and increment that representation programatically.

e.g. 
If the first digit is a zero, change that to a one.
If there is only one digit, and the digit is 1, add a zero (to the right).
...
If all the values are 1, change all the values after the first to zero.
etc.

Note:
if rules can be devised to do the same with hex representation of bytes with two letters, that could conserve memory further.

# "It's tape all the way down."
Assuming we do not run out of "tape" (as in the Turing machine ribbon), we should be able to represent arbitrarily large values without the memory-management issue of having a fixed-size number type, such as u8 or u64.

Argubably, values such as time-stamps should be planned for in this way, so that planning failures such as the y2k bug and the unix-epoch rollover. Do not happen.

While a number 'value' may be 'too big' to store, such as u512, the representation of that value is entirely manageable, even on a system with extreme resource constraints. Any machine that can process a file the size of a page of printed characters can compute and compute with values the representation of which fits on that page.


# With output in:
- binary
- hex
- decimal

# Memory Topic Outline:
1. stack is ~2x faster than heap but has a potential ceiling and maybe more importantly has a larger than usually needed pre-allocated buffer.

Hex is lower than decimal, faster than binary, but uses progressively less memory to store larger numbers.

### Counting to N: we need approximately...
Binary:   ⌈log₂(N)⌉ bytes     (most bytes)
Decimal:  ⌈log₁₀(N)⌉ bytes    (middle)
Hex:      ⌈log₁₆(N)⌉ bytes    (fewest bytes)


e.g.
```
10:          Decimal="10" (2 bytes), Hex="A" (1 byte)      → Hex 50% smaller
100:         Decimal="100" (3 bytes), Hex="64" (2 bytes)   → Hex 33% smaller  
1000:        Decimal="1000" (4 bytes), Hex="3E8" (3 bytes) → Hex 25% smaller
1,000,000:   Decimal=7 bytes, Hex=5 bytes                  → Hex 29% smaller
1,000,000,000: Decimal=10 bytes, Hex=8 bytes               → Hex 20% smaller
```



# Example Production version:


## Externalized Cascading Buffer Hex Counter: procedural_external_hexcascade_counter

To minimize active memory but be capable of rather large numbers, but also keeping the code simple:

1. starting with small buffer
2. starting again with larger buffer if that buffer fills



