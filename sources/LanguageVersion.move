address StarcoinFramework {
module LanguageVersion {
    spec module {
        pragma verify;
        pragma aborts_if_is_strict;
    }

    struct LanguageVersion has copy, drop, store {
        major: u64,
    }

    public fun new(version: u64): LanguageVersion {
        LanguageVersion {major: version}
    }
    spec new {
        aborts_if false;
        ensures result.major == version;
    }

    public fun version(version: &LanguageVersion): u64 {
        version.major
    }
    spec version {
        aborts_if false;
        ensures result == version.major;
    }
}
}