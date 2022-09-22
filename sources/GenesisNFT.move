module StarcoinFramework::GenesisNFT {
    use StarcoinFramework::IdentifierNFT;
    use StarcoinFramework::Option::Option;
    use StarcoinFramework::NFT::{Self, MintCapability};
    use StarcoinFramework::MerkleNFTDistributor;
    use StarcoinFramework::CoreAddresses;
    use StarcoinFramework::Signer;

    spec module {
        pragma verify = true;
        pragma aborts_if_is_strict = true;
    }

    struct GenesisNFT has store{}
    struct GenesisNFTMeta has copy, store, drop{
        index: u64
    }
    struct GenesisNFTInfo has key, copy, store, drop{
        merkle_root: vector<u8>,
        total_supply: u64,
    }
    struct GenesisNFTMintCapability has key{
        cap: MintCapability<GenesisNFTMeta>
    }


    public fun initialize(sender: &signer, merkle_root: vector<u8>, leafs: u64, image: vector<u8>){
        CoreAddresses::assert_genesis_address(sender);
        let metadata = NFT::new_meta_with_image(b"StarcoinGenesisNFT", image, b"The starcoin genesis NFT");
        let  nft_info = GenesisNFTInfo{merkle_root: *&merkle_root, total_supply: leafs};
        let cap = MerkleNFTDistributor::register<GenesisNFTMeta, GenesisNFTInfo>(sender, merkle_root, leafs, nft_info, metadata);
        move_to(sender, GenesisNFTMintCapability{cap});
    }

    spec initialize {
        pragma aborts_if_is_partial = true;
        include AbortsIfNotGenesisAddress{ account: sender };
        aborts_if exists<GenesisNFTMintCapability>(Signer::address_of(sender));
        ensures exists<GenesisNFTMintCapability>(Signer::address_of(sender));
    }

    spec schema AbortsIfNotGenesisAddress {
        account: signer;
        aborts_if Signer::address_of(account) != CoreAddresses::SPEC_GENESIS_ADDRESS();
    }

    public fun upgrade_to_nft_type_info_v2(sender: &signer) acquires GenesisNFTMintCapability{
        CoreAddresses::assert_genesis_address(sender);
        let cap = borrow_global_mut<GenesisNFTMintCapability>(CoreAddresses::GENESIS_ADDRESS());
        NFT::upgrade_nft_type_info_from_v1_to_v2<GenesisNFTMeta, GenesisNFTInfo>(sender, &mut cap.cap);
        let nft_info = NFT::remove_compat_info<GenesisNFTMeta, GenesisNFTInfo>(&mut cap.cap);
        move_to(sender, nft_info);
    }

    spec upgrade_to_nft_type_info_v2 {
        pragma aborts_if_is_partial = true;
        include AbortsIfNotGenesisAddress{ account: sender };
        aborts_if !exists<GenesisNFTMintCapability>(CoreAddresses::GENESIS_ADDRESS());
        aborts_if exists<GenesisNFTInfo>(Signer::address_of(sender));
        ensures exists<GenesisNFTInfo>(Signer::address_of(sender));
    }

    public fun mint(sender: &signer, index: u64, merkle_proof:vector<vector<u8>>)
        acquires GenesisNFTMintCapability{
        let metadata = NFT::empty_meta();
        let cap = borrow_global_mut<GenesisNFTMintCapability>(CoreAddresses::GENESIS_ADDRESS());
        let nft = MerkleNFTDistributor::mint_with_cap<GenesisNFTMeta, GenesisNFT, GenesisNFTInfo>(
            sender, 
            &mut cap.cap, 
            CoreAddresses::GENESIS_ADDRESS(), 
            index,
            metadata, 
            GenesisNFTMeta{index}, 
            GenesisNFT{}, 
            merkle_proof,
        );
        IdentifierNFT::grant(&mut cap.cap, sender, nft);
    }

    spec mint {
        pragma aborts_if_is_partial = true;
        aborts_if !exists<GenesisNFTMintCapability>(CoreAddresses::GENESIS_ADDRESS());
    }

    public fun verify(account: address, index: u64, merkle_proof: vector<vector<u8>>): bool {
        MerkleNFTDistributor::verify_proof<GenesisNFTMeta>(account, CoreAddresses::GENESIS_ADDRESS(), index, merkle_proof)
    }
    spec verify {
        pragma aborts_if_is_partial = true;
    }

    public fun get_info(owner: address): Option<NFT::NFTInfo<GenesisNFTMeta>>{
        IdentifierNFT::get_nft_info<GenesisNFTMeta, GenesisNFT>(owner)
    }

    public fun is_minted(index: u64): bool {
        let creator = CoreAddresses::GENESIS_ADDRESS();
        MerkleNFTDistributor::is_minted<GenesisNFTMeta>(creator, index)
    }

    spec is_minted {
        pragma aborts_if_is_partial = true;
    }

    public fun genesis_nft_info(): GenesisNFTInfo acquires GenesisNFTInfo{
        *borrow_global<GenesisNFTInfo>(CoreAddresses::GENESIS_ADDRESS())
    }

    spec genesis_nft_info {
        aborts_if !exists<GenesisNFTInfo>(CoreAddresses::GENESIS_ADDRESS());
    }
}

module StarcoinFramework::GenesisNFTScripts {
    use StarcoinFramework::GenesisNFT;
    use StarcoinFramework::CoreAddresses;

    spec module {
        pragma verify;
        pragma aborts_if_is_strict;
    }

    /// Mint a GenesisNFT
    public(script) fun mint(sender: signer, index: u64, merkle_proof:vector<vector<u8>>) {
        GenesisNFT::mint(&sender, index, merkle_proof);
    }

    spec mint {
        pragma aborts_if_is_partial = true;
        aborts_if !exists<GenesisNFT::GenesisNFTMintCapability>(CoreAddresses::GENESIS_ADDRESS());
    }

}
