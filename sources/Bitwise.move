address StarcoinFramework {
/// Functions for bit operations.
module BitOperators {

    spec module {
        // We don't verify this module because currently MVP cannot reason about most bitwise operations.
        pragma verify = false;
    }

    /// bit and: x & y
    public fun and(x: u64, y: u64): u64 {
        x & y
    }

    /// bit or: x | y
    public fun or(x: u64, y: u64): u64 {
        x | y
    }

    /// bit xor: x ^ y
    public fun xor(x: u64, y: u64): u64 {
        x ^ y
    }

    /// bit not: !x
    public fun not(x: u64): u64 {
       x ^ 0xffffffffffffffff
    }

    /// left shift n bits.
    public fun lshift(x: u64, n: u8): u64 {
        x << n
    }

    /// right shift n bits.
    public fun rshift(x: u64, n: u8): u64 {
        x >> n
    }
}
}