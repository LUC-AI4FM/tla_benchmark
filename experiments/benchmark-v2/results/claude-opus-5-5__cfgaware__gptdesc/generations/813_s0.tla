---------------------------- MODULE APAParReach ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Set(Int);
    Nodes,
    \* @type: Int -> Set(Int);
    Succ,
    \* @type: Int;
    Root,
    \* @type: Set(Str);
    Procs

VARIABLES
    \* @type: Set(Int);
    marked,
    \* @type: Set(Int);
    vroot,
    \* @type: Str -> Int;
    u,
    \* @type: Str -> Set(Int);
    toVroot,
    \* @type: Str -> Str;
    pc

\* Concrete constant values used to instantiate the constants above.

NodesVal == {1, 2, 3, 4}

SuccVal == [ n \in NodesVal |->
               IF n = 1 THEN {2, 3}
               ELSE IF n = 2 THEN {4}
               ELSE IF n = 3 THEN {4}
               ELSE {} ]

RootVal == 1

ProcsVal == {"p1", "p2"}

\* Instantiate the parallel reachability specification with the
\* annotated constants and variables of this module. Its definitions,
\* including Init, Next and Inv, become available in this module.

INSTANCE ParReach
    WITH Nodes   <- Nodes,
         Succ    <- Succ,
         Root    <- Root,
         Procs   <- Procs,
         marked  <- marked,
         vroot   <- vroot,
         u       <- u,
         toVroot <- toVroot,
         pc      <- pc

=============================================================================