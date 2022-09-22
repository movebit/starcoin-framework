address StarcoinFramework {
/// Onchain configuration for timeout setting of transaction.
module TransactionTimeoutConfig {
    use StarcoinFramework::Timestamp;
    use StarcoinFramework::CoreAddresses;
    use StarcoinFramework::Config;
    use StarcoinFramework::Signer;

    spec module {
        pragma verify;
        pragma aborts_if_is_strict;
    }

    /// config structs.
    struct TransactionTimeoutConfig has copy, drop, store {
        /// timeout in second.
        duration_seconds: u64,
    }

    /// Initialize function. Should only be called in genesis.
    public fun initialize(account: &signer, duration_seconds: u64) {
        Timestamp::assert_genesis();
        CoreAddresses::assert_genesis_address(account);

        Config::publish_new_config<Self::TransactionTimeoutConfig>(
            account,
            new_transaction_timeout_config(duration_seconds)
        );
    }

    spec initialize {
        aborts_if !Timestamp::is_genesis();
        aborts_if Signer::address_of(account) != CoreAddresses::GENESIS_ADDRESS();
        include Config::PublishNewConfigAbortsIf<TransactionTimeoutConfig>;
        include Config::PublishNewConfigEnsures<TransactionTimeoutConfig>;
    }

    /// Create a new timeout config used in dao proposal.
    public fun new_transaction_timeout_config(duration_seconds: u64) : TransactionTimeoutConfig {
        TransactionTimeoutConfig { duration_seconds }
    }

    spec new_transaction_timeout_config {
        aborts_if false;
    }

    /// Get current timeout config.
    public fun get_transaction_timeout_config(): TransactionTimeoutConfig {
        Config::get_by_address<TransactionTimeoutConfig>(CoreAddresses::GENESIS_ADDRESS())
    }

    spec get_transaction_timeout_config {
        let addr = CoreAddresses::SPEC_GENESIS_ADDRESS();
        include Config::AbortsIfConfigNotExist<TransactionTimeoutConfig>;
        ensures result == Config::get_by_address<TransactionTimeoutConfig>(addr);
    }

    /// Get current txn timeout in seconds.
    public fun duration_seconds() :u64 {
        get_transaction_timeout_config().duration_seconds
    }

    spec duration_seconds {
        let addr = CoreAddresses::SPEC_GENESIS_ADDRESS();
        include Config::AbortsIfConfigNotExist<TransactionTimeoutConfig>;
        ensures result == Config::get_by_address<TransactionTimeoutConfig>(addr).duration_seconds;
    }

    spec schema AbortsIfTxnTimeoutConfigNotExist {
        include Config::AbortsIfConfigNotExist<TransactionTimeoutConfig>{
            addr: CoreAddresses::SPEC_GENESIS_ADDRESS()
        };
    }
}
}