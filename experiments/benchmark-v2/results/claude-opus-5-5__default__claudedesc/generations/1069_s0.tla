---------------------- MODULE AsyncTerminationDetection ---------------------
(***************************************************************************)
(* An abstract specification of the termination detection problem in a    *)
(* ring of N nodes with asynchronous message passing.                      *)
(*                                                                         *)
(* Model checked with N = 4 and the state constraint StateConstraint,      *)
(* which bounds the number of pending messages at each node to at most 3.  *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Int;
    N

ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES
    \* @type: Int -> Bool;
    active,               \* activation status of each node
    \* @type: Int -> Int;
    pending,              \* number of messages pending delivery at each node
    \* @type: Bool;
    terminationDetected   \* has termination been detected?

vars == << active, pending, terminationDetected >>

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> Nat]
    /\ terminationDetected \in BOOLEAN

\* The system is truly terminated: all nodes inactive, no messages in flight.
terminated ==
    \A n \in Node : ~ active[n] /\ pending[n] = 0

-----------------------------------------------------------------------------

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending = [i \in Node |-> 0]
    /\ terminationDetected \in {FALSE, terminated}

Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ pending' = pending
    \* possibly (but not necessarily) detect termination if all nodes are inactive
    /\ terminationDetected' \in {terminationDetected, terminated'}

SendMsg(i, j) ==
    /\ active[i]
    /\ pending' = [pending EXCEPT ![j] = @ + 1]
    /\ UNCHANGED << active, terminationDetected >>

RcvMsg(i) ==
    /\ pending[i] > 0
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ UNCHANGED terminationDetected

DetectTermination ==
    /\ terminated
    /\ terminationDetected' = TRUE
    /\ UNCHANGED << active, pending >>

Next ==
    \/ \E i \in Node : Terminate(i)
    \/ \E i, j \in Node : SendMsg(i, j)
    \/ \E i \in Node : RcvMsg(i)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------

\* State constraint for model checking (pending counts bounded by 3).
StateConstraint ==
    \A i \in Node : pending[i] <= 3

\* Safety: termination is only detected if the system has truly terminated.
Safe == terminationDetected => terminated

\* Liveness: true termination is eventually detected.
Live == terminated ~> terminationDetected

\* Quiescence: once terminated, the system remains terminated.
Quiescence == [](terminated => []terminated)

\* Action-formula variants of quiescence.
QuiescenceAsActionInv == terminated => terminated'

QuiescenceAsTraceInv == [][terminated => terminated']_vars

\* Inductive invariant for Apalache verification.
IndInv ==
    /\ TypeOK
    /\ Safe

\* Initialization predicate for Apalache inductiveness checks.
IndInit ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> 0..3]
    /\ terminationDetected \in BOOLEAN
    /\ IndInv

THEOREM Spec => []TypeOK
THEOREM Spec => []Safe
THEOREM Spec => Live
THEOREM Spec => Quiescence
=============================================================================