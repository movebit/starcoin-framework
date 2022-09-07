address StarcoinFramework {
/// Deprecated since @v3 please use Collection2
/// Provide a account based vector for save resource.
module Collection {
    use StarcoinFramework::Signer;
    use StarcoinFramework::Errors;
    use StarcoinFramework::Vector;
    use StarcoinFramework::Option::{Self, Option};

    spec module {
        pragma verify = true;
        pragma aborts_if_is_strict = true;
    }

    /// Collection in memory, can not drop & store.
    struct Collection<T>{
        items:vector<T>,
        /// the owner of Collection.
        owner: address,
    }

    /// Collection in global store.
    struct CollectionStore<T: store> has key {
        /// items in the CollectionStore.
        /// use Option at  here is for temporary take away from store to construct Collection.
        items: Option<vector<T>>,
    }

    const EDEPRECATED_FUNCTION: u64 = 19;

    const ECOLLECTION_NOT_EXIST: u64 = 101;
    /// The operator require the collection owner.
    const ECOLLECTION_NOT_OWNER: u64 = 102;

    /// Acquire an immutable reference to the `i`th element of the collection `c`.
    /// Aborts if `i` is out of bounds.
    public fun borrow<T>(c: &Collection<T>, i: u64): &T{
        Vector::borrow(&c.items, i)
    }

    spec borrow {
        aborts_if i < 0;
        aborts_if i >= len(c.items);
        ensures result == c.items[i];
    }

    /// Pop an element from the end of vector `v`.
    /// Aborts if `v` is empty.
    public fun pop_back<T>(account: &signer, c: &mut Collection<T>): T {
        assert!(Signer::address_of(account) == c.owner, Errors::requires_address(ECOLLECTION_NOT_OWNER));
        Vector::pop_back<T>(&mut c.items)
    }

    spec pop_back {
        let length = len(c.items);
        let post new_length = len(c.items);

        let last = c.items[length - 1];
        aborts_if Signer::address_of(account) != c.owner;
        aborts_if length == 0;
        ensures length == new_length + 1;
        ensures result == last;
    }

    /// check the Collection exists in `addr`
    fun exists_at<T: store>(addr: address): bool{
        exists<CollectionStore<T>>(addr)
    }

    spec exists_at {
        aborts_if false;
    }

    /// Deprecated since @v3
    /// Put items to account's Collection last position.
    public fun put<T: store>(_account: &signer, _item: T) {
        abort Errors::deprecated(EDEPRECATED_FUNCTION)
    }

    spec put {
        aborts_if true;
    }

    /// Take last item from account's Collection of T.
    public fun take<T: store>(account: &signer): T acquires CollectionStore{
        let addr = Signer::address_of(account);
        let c = borrow_collection<T>(addr);
        let item = pop_back(account, &mut c);
        return_collection(c);
        item
    }

    spec take {
        let addr = Signer::address_of(account);
        let old_len = len(Option::borrow(global<CollectionStore<T>>(addr).items));
        aborts_if !exists<CollectionStore<T>>(addr);
        aborts_if Option::is_none(global<CollectionStore<T>>(addr).items);
        aborts_if old_len == 0;

        ensures if (old_len > 1) {
            Option::borrow(old(global<CollectionStore<T>>(addr)).items) ==
            concat(Option::borrow(global<CollectionStore<T>>(addr).items), vec(result))
        } else {
            Option::borrow(old(global<CollectionStore<T>>(addr)).items) == vec(result)
        };
    }

    /// Borrow collection of T from `addr`
    public fun borrow_collection<T: store>(addr: address): Collection<T> acquires CollectionStore{
        assert!(exists_at<T>(addr), Errors::invalid_state(ECOLLECTION_NOT_EXIST));
        let c = borrow_global_mut<CollectionStore<T>>(addr);
        let items = Option::extract(&mut c.items);
        Collection {
            items,
            owner: addr
        }
    }

    spec borrow_collection {
        let pre_items = global<CollectionStore<T>>(addr).items;
        let post post_items = global<CollectionStore<T>>(addr).items;
        aborts_if !exists<CollectionStore<T>>(addr);
        aborts_if Option::is_none(pre_items);
        ensures Option::is_none(post_items);
        ensures result.items == Option::borrow(old(global<CollectionStore<T>>(addr).items));
        ensures result.owner == addr;
    }

    /// Return the Collection of T
    public fun return_collection<T: store>(c: Collection<T>) acquires CollectionStore{
        let Collection{ items, owner } = c;
        if (Vector::is_empty(&items)) {
            let c = move_from<CollectionStore<T>>(owner);
            destroy_empty(c);
            Vector::destroy_empty(items);
        } else {
            let c = borrow_global_mut<CollectionStore<T>>(owner);
            Option::fill(&mut c.items, items);
        }
    }

    spec return_collection {
        aborts_if !exists<CollectionStore<T>>(c.owner);
        aborts_if Option::is_some(borrow_global<CollectionStore<T>>(c.owner).items);

        ensures if (len(c.items) == 0) {
            !exists<CollectionStore<T>>(c.owner)
        } else {
            Option::borrow(borrow_global<CollectionStore<T>>(c.owner).items) == c.items
        };
    }

    fun destroy_empty<T: store>(c: CollectionStore<T>){
        let CollectionStore{ items } = c;
        Option::destroy_none(items);
    }

    spec destroy_empty {
        aborts_if Option::is_some(c.items);
    }

}
}
