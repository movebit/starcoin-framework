address StarcoinFramework{
/// The module provide a dummy token implementation.
module DummyToken {
    use StarcoinFramework::Token::{Self, Token};
    use StarcoinFramework::Errors;

    spec module {
        pragma verify;
        pragma aborts_if_is_strict;
    }

    /// The DummyToken type.
    struct DummyToken has copy, drop, store { }


    const EMINT_TOO_MUCH:u64 = 101;

    const PRECISION: u8 = 3;

    /// Burn capability of the token.
    struct SharedBurnCapability has key {
        cap: Token::BurnCapability<DummyToken>,
    }

    /// Mint capability of the token.
    struct SharedMintCapability has key, store {
        cap: Token::MintCapability<DummyToken>,
    }

    /// Initialization of the module.
    public fun initialize(account: &signer) {
        Token::register_token<DummyToken>(
            account,
            PRECISION,
        );

        let burn_cap = Token::remove_burn_capability<DummyToken>(account);
        move_to(account, SharedBurnCapability{cap: burn_cap});

        let burn_cap = Token::remove_mint_capability<DummyToken>(account);
        move_to(account, SharedMintCapability{cap: burn_cap});
    }

    spec initialize {
        include Token::RegisterTokenAbortsIf<DummyToken>{ precision: PRECISION };
        include Token::RegisterTokenEnsures<DummyToken>;
    }

    /// Returns true if `TokenType` is `DummyToken::DummyToken`
    public fun is_dummy_token<TokenType: store>(): bool {
        Token::is_same_token<DummyToken, TokenType>()
    }

    spec is_dummy_token {
        // Sadly we cannot specify the result because MVP cannot use template type info.
        aborts_if false;
    }

    /// Burn the given token.
    public fun burn(token: Token<DummyToken>) acquires SharedBurnCapability {
        let cap = borrow_global<SharedBurnCapability>(token_address());
        Token::burn_with_capability(&cap.cap, token);
    }

    spec burn {
        let addr = Token::SPEC_TOKEN_TEST_ADDRESS();
        aborts_if !exists<SharedBurnCapability>(addr);
        // Maybe refactor this. Mostly duplicate with Config::burn_with_capability.
        aborts_if Token::spec_abstract_total_value<DummyToken>() - token.value < 0;
        ensures Token::spec_abstract_total_value<DummyToken>() ==
            old(global<Token::TokenInfo<DummyToken>>(addr).total_value) - token.value;
    }

    /// Anyone can mint DummyToken, amount should < 10000
    public fun mint(_account: &signer, amount: u128) : Token<DummyToken> acquires SharedMintCapability {
        assert!(amount <= 10000, Errors::invalid_argument(EMINT_TOO_MUCH));
        let cap = borrow_global<SharedMintCapability>(token_address());
        Token::mint_with_capability(&cap.cap, amount)
    }

    spec mint {
        let addr = Token::SPEC_TOKEN_TEST_ADDRESS();
        aborts_if amount > 10000;
        aborts_if !exists<SharedMintCapability>(addr);
        aborts_if Token::spec_abstract_total_value<DummyToken>() + amount > MAX_U128;
        ensures result.value == amount;
        ensures Token::spec_abstract_total_value<DummyToken>() ==
                old(global<Token::TokenInfo<DummyToken>>(addr).total_value) + amount;
    }

    /// Return the token address.
    public fun token_address(): address {
        Token::token_address<DummyToken>()
    }

    spec token_address {
        aborts_if false;
        ensures exists<Token::TokenInfo<DummyToken>>(result);
        ensures result == Token::SPEC_TOKEN_TEST_ADDRESS();
        ensures global<Token::TokenInfo<DummyToken>>(result).total_value == 100000000u128;
    }
}

module DummyTokenScripts{
    use StarcoinFramework::DummyToken::{Self, DummyToken};
    use StarcoinFramework::Account;
    use StarcoinFramework::Signer;

    spec module {
        pragma verify = false;
    }

    public(script) fun mint(sender: signer, amount: u128) {
        let token = DummyToken::mint(&sender, amount);
        let sender_addr = Signer::address_of(&sender);
        if (Account::is_accept_token<DummyToken>(sender_addr)) {
            Account::do_accept_token<DummyToken>(&sender);
        };
        Account::deposit(sender_addr, token);
    }

    spec mint {
        pragma aborts_if_is_partial = true;

        let sender_addr = Signer::address_of(sender);

        aborts_if amount > 10000;

        // Fix the spec of account to add more postconditions
        //let old_balance = global<Account::Balance<DummyToken>>(sender_addr).token.value;
        //let post new_balance = global<Account::Balance<DummyToken>>(sender_addr).token.value;

        //ensures new_balance == old_balance + amount;
    }
}
}
