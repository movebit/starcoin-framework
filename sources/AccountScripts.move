address StarcoinFramework {
module AccountScripts {
    use StarcoinFramework::Account;
    use StarcoinFramework::Signer;
    /// Enable account's auto-accept-token feature.
    /// The script function is reenterable.
    public(script) fun enable_auto_accept_token(account: signer) {
        Account::set_auto_accept_token(&account, true);
    }
    spec enable_auto_accept_token {
        aborts_if false;
        let addr = Signer::address_of(account);
        ensures global<Account::AutoAcceptToken>(addr).enable;
    }

    /// Disable account's auto-accept-token feature.
    /// The script function is reenterable.
    public(script) fun disable_auto_accept_token(account: signer) {
        Account::set_auto_accept_token(&account, false);
    }
    spec disable_auto_accept_token {
        aborts_if false;
        let addr = Signer::address_of(account);
        ensures !global<Account::AutoAcceptToken>(addr).enable;
    }
}
}
