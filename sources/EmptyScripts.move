address StarcoinFramework {
    // A empty scripts module for call a script but do nothing.
    module EmptyScripts {

        spec module {
            pragma verify = true;
            pragma aborts_if_is_strict = true;
        }

        public(script) fun empty_script() {}

        spec empty_script {}
    }
}