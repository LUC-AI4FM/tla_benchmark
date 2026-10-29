---- MODULE MCCheckpointCoordination ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Node,           \* set of nodes (model values)
    MaxNat,         \* bound on natural numbers explored
    MaxLogIndex     \* bound on log indices explored

VARIABLES
    leader,         \* current leader node (or a NoNode value)
    lease,          \* current lease record: [holder |-> n, term |-> t]
    log,            \* function from log index to entry state
    checkpoint,     \* checkpoint index agreed so far
    messages        \* set of in-flight messages

vars == << leader, lease, log, checkpoint, messages >>

----------------------------------------------------------------------------
(* Instantiation of the underlying checkpoint coordination specification. *)

CC == INSTANCE CheckpointCoordination

----------------------------------------------------------------------------
(* Bounded ranges used to override Nat and the log-index range in the model *)

MCNat == 0 .. MaxNat

MCLogIndex == 1 .. MaxLogIndex

----------------------------------------------------------------------------
(* State constraint: there must always be at least one open index.        *)

OpenIndices == { i \in MCLogIndex : i \in DOMAIN log /\ log[i] = "open" }

StateConstraint == OpenIndices # {}

----------------------------------------------------------------------------
(* Symmetry set over nodes.                                                *)

NodeSymmetry == Permutations(Node)

----------------------------------------------------------------------------
(* BAD OPTIMIZATION: allow a lease to be replaced whenever it is held by   *)
(* the current leader, in addition to the cases permitted by the original  *)
(* specification. This is intentionally incorrect and is expected to cause *)
(* the safety invariants to be violated during model checking.            *)

BadCanReplaceLease(l) ==
    \/ CC!CanReplaceLease(l)
    \/ l.holder = leader

----------------------------------------------------------------------------
(* Behaviour is delegated to the instantiated module.                      *)

Init == CC!Init

Next == CC!Next

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----------------------------------------------------------------------------
(* Properties delegated to the instantiated module.                        *)

TypeOK == CC!TypeOK

Safety == CC!Safety

Liveness == CC!Liveness

THEOREM Spec => [](TypeOK /\ Safety)

====