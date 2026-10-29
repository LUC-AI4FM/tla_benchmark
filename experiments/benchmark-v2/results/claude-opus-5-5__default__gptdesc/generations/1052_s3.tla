---- MODULE APTokenRing ----
EXTENDS Integers

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Int;
    M

VARIABLES
    \* @type: Int -> Int;
    c

vars == << c >>

INSTANCE TokenRing

====