------------------------------- MODULE EWD998 -------------------------------
(***************************************************************************)
(* TLA+ specification of Safra's algorithm for distributed termination     *)
(* detection on a ring, as described in EWD 998.                           *)
(*                                                                         *)
(* N nodes, numbered 0..N-1, form a ring. Node 0 is the initiator. The     *)
(* token travels from node i to node i-1. Each node can be active or       *)
(* passive and is colored white or black. Each node keeps a counter of     *)
(* the messages it sent minus the messages it received. The token carries  *)
(* its position, a color and an accumulated counter q.                     *)
(***************************************************************************)
EXTENDS Integers, Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES
    active,   \* active[i]  : is node i active?
    color,    \* color[i]   : color of node i
    counter,  \* counter[i] : messages sent minus messages received by i
    pending,  \* pending[i] : messages in flight addressed to node i
    token     \* the token: [pos, q, color]

vars == <<active, color, counter, pending, token>>

-----------------------------------------------------------------------------
(* Sum of f[x] for x in the finite set S. *)
RECURSIVE SumSet(_, _)
SumSet(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN  f[x] + SumSet(f, S \ {x})

-----------------------------------------------------------------------------
TypeOK ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ counter \in [Node -> Int]
    /\ pending \in [Node -> Nat]
    /\ token   \in [pos : Node, q : Int, color : Color]

Init ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ counter = [i \in Node |-> 0]
    /\ pending = [i \in Node |-> 0]
    /\ token   = [pos |-> 0, q |-> 0, color |-> "black"]

-----------------------------------------------------------------------------
(* Node 0 starts a new probe if the previous one was inconclusive. *)
InitiateProbe ==
    /\ token.pos = 0
    /\ \/ token.color = "black"
       \/ color[0] = "black"
       \/ counter[0] + token.q > 0
    /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED <<active, counter, pending>>

(* Node i (i # 0) passes the token to node i-1 once it is passive. *)
PassToken(i) ==
    /\ i # 0
    /\ token.pos = i
    /\ \/ ~ active[i]
       \/ color[i] = "black"
       \/ pending[i] > 0
    /\ token' = [pos   |-> i - 1,
                 q     |-> token.q + counter[i],
                 color |-> IF color[i] = "black" THEN "black" ELSE token.color]
    /\ color' = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED <<active, counter, pending>>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------
(* An active node i sends a message to some other node j. *)
SendMsg(i) ==
    /\ active[i]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ \E j \in Node \ {i} :
          pending' = [pending EXCEPT ![j] = @ + 1]
    /\ UNCHANGED <<active, color, token>>

(* Node i receives a message, becomes active and turns black. *)
RecvMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ color'   = [color EXCEPT ![i] = "black"]
    /\ active'  = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED token

(* An active node becomes passive. *)
Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, counter, pending, token>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------
Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(* Bounds for model checking. *)
MaxCounter == 3

StateConstraint ==
    /\ \A i \in Node : counter[i] <= MaxCounter /\ pending[i] <= MaxCounter
    /\ token.q \in -MaxCounter .. MaxCounter

ActionConstraint ==
    \A i \in Node : counter'[i] - counter[i] \in -1 .. 1

-----------------------------------------------------------------------------
(* Correctness properties. *)
terminated == \A i \in Node : ~ active[i] /\ pending[i] = 0

terminationDetected ==
    /\ token.pos = 0
    /\ token.color = "white"
    /\ token.q + counter[0] = 0
    /\ color[0] = "white"
    /\ ~ active[0]

(* Safety: termination is only detected if the system has terminated. *)
TerminationDetection == terminationDetected => terminated

(* Once terminated, the system stays terminated. *)
StableTermination == [][terminated => terminated']_vars

(* Liveness: termination is eventually detected. *)
Liveness == terminated ~> terminationDetected

-----------------------------------------------------------------------------
(* Inductive invariant capturing Safra's correctness argument. *)
Rng(a, b) == {i \in Node : a <= i /\ i <= b}

Inv ==
    /\ SumSet(pending, Node) = SumSet(counter, Node)
    /\ \/ /\ \A i \in Rng(token.pos + 1, N - 1) : ~ active[i]
          /\ token.q = SumSet(counter, Rng(token.pos + 1, N - 1))
       \/ SumSet(counter, Rng(0, token.pos)) + token.q > 0
       \/ \E i \in Rng(0, token.pos) : color[i] = "black"
       \/ token.color = "black"

IndInv == TypeOK /\ Inv

THEOREM Spec => [](TypeOK /\ Inv /\ TerminationDetection)
THEOREM Spec => Liveness
=============================================================================