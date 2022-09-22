module StarcoinFramework::GenesisSignerCapability {
    use StarcoinFramework::Account;
    use StarcoinFramework::CoreAddresses;
    use StarcoinFramework::Errors;
    use StarcoinFramework::Signer;

    friend StarcoinFramework::NFT;
    friend StarcoinFramework::Oracle;
    friend StarcoinFramework::Genesis;
    friend StarcoinFramework::StdlibUpgradeScripts;

    spec module {
        pragma verify = true;
        pragma aborts_if_is_strict = true;
    }

    const ENOT_GENESIS_ACCOUNT: u64 = 11;

    struct GenesisSignerCapability has key {
        cap: Account::SignerCapability,
    }

    public(friend) fun initialize(signer:&signer, cap: Account::SignerCapability) {
        CoreAddresses::assert_genesis_address(signer);
        assert!(Account::signer_address(&cap) == CoreAddresses::GENESIS_ADDRESS(), Errors::invalid_argument(ENOT_GENESIS_ACCOUNT));
        move_to(signer, GenesisSignerCapability{cap});
    }

    spec schema AbortsIfNotGenesisAddress {
        account: signer;
        aborts_if Signer::address_of(account) != CoreAddresses::SPEC_GENESIS_ADDRESS();
    }

    spec initialize {
        include AbortsIfNotGenesisAddress{ account: signer };
        aborts_if Account::signer_address(cap) != CoreAddresses::SPEC_GENESIS_ADDRESS();
        aborts_if exists<GenesisSignerCapability>(Signer::address_of(signer));
        ensures exists<GenesisSignerCapability>(Signer::address_of(signer));
    }

    public(friend) fun get_genesis_signer(): signer acquires GenesisSignerCapability {
        let cap = borrow_global<GenesisSignerCapability>(CoreAddresses::GENESIS_ADDRESS());
        Account::create_signer_with_cap(&cap.cap)
    }

    spec get_genesis_signer {
        aborts_if !exists<GenesisSignerCapability>(CoreAddresses::SPEC_GENESIS_ADDRESS());
    }
}
