address StarcoinFramework {
/// The module provide configuration for block reward.
module RewardConfig {
    use StarcoinFramework::Timestamp;
    use StarcoinFramework::Signer;
    use StarcoinFramework::CoreAddresses;
    use StarcoinFramework::Config;

    spec module {
        pragma verify;
        pragma aborts_if_is_strict;
    }

    /// Reward configuration
    struct RewardConfig has copy, drop, store {
        /// how many blocks delay reward distribution.
        reward_delay: u64,
    }

    const EINVALID_ARGUMENT: u64 = 18;

    /// Module initialization.
    public fun initialize(account: &signer, reward_delay: u64) {
        Timestamp::assert_genesis();
        CoreAddresses::assert_genesis_address(account);

        Config::publish_new_config<Self::RewardConfig>(
            account,
            new_reward_config(reward_delay)
        );
    }

    spec initialize {
        aborts_if !Timestamp::is_genesis();
        aborts_if Signer::address_of(account) != CoreAddresses::GENESIS_ADDRESS();
        aborts_if exists<Config::Config<RewardConfig>>(Signer::address_of(account));
        include Config::PublishNewConfigAbortsIf<RewardConfig>;
        include Config::PublishNewConfigEnsures<RewardConfig>;
    }

    /// Create a new reward config mainly used in DAO.
    public fun new_reward_config(reward_delay: u64) : RewardConfig {
        RewardConfig {reward_delay}
    }

    spec new_reward_config {
        aborts_if false;
        ensures result.reward_delay == reward_delay;
    }

    /// Get reward configuration.
    public fun get_reward_config(): RewardConfig {
        Config::get_by_address<RewardConfig>(CoreAddresses::GENESIS_ADDRESS())
    }

    spec get_reward_config {
        let addr = CoreAddresses::GENESIS_ADDRESS();
        aborts_if !Config::spec_exists<RewardConfig>(addr);
        ensures result == Config::spec_get<RewardConfig>(addr);
    }

    /// Get reward delay.
    public fun reward_delay() :u64 {
        get_reward_config().reward_delay
    }

    spec reward_delay {
        let addr = CoreAddresses::GENESIS_ADDRESS();
        aborts_if !Config::spec_exists<RewardConfig>(addr);
        ensures result == Config::spec_get<RewardConfig>(addr).reward_delay;
    }
}
}
