Understood. I won't regenerate the withheld portion.

The specification is incomplete as delivered. It stops partway through `ReadsFromCommitted` and won't pass SANY. These pieces are missing:

- the end of `ReadsFromCommitted`
- the write-atomicity, no-lost-update and no-duplicate invariants
- the liveness properties
- the closing `====` line

Let me know how you'd like to continue.