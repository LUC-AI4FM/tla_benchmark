------------------------------- MODULE EWD998 -------------------------------
(***************************************************************************)
(* Safra's algorithm for distributed termination detection on a ring,     *)
(* as described in EWD 998.                                                *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES
  active,   \* active[i]: is node i active?
  color,    \* color[i]: color of node i
  counter,  \* counter[i]: messages sent minus messages received by node i
  pending,  \* pending[i]: number of messages in transit to node i
  token     \* the token: position, counter q, and color

vars == <<active, color, counter, pending, token>>

TypeOK ==
  /\ active  \in [Node -> BOOLEAN]
  /\ color   \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ pending \in [Node -> Nat]
  /\ token   \in [pos : Node, q : Int, color : Color]

---------------------------------------------------------------------------
(* Helper: sum of f[x] over x \in S *)
RECURSIVE SumF(_, _)
SumF(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  f[x] + SumF(f, S \ {x})

---------------------------------------------------------------------------
Init ==
  /\ active  \in [Node -> BOOLEAN]
  /\ color   \in [Node -> Color]
  /\ counter = [i \in Node |-> 0]
  /\ pending = [i \in Node |-> 0]
  /\ token   = [pos |-> 0, q |-> 0, color |-> "black"]

(* Node 0 initiates a new probe if the previous one was inconclusive. *)
InitiateProbe ==
  /\ token.pos = 0
  /\ \/ token.color = "black"
     \/ color[0] = "black"
     \/ counter[0] + token.q > 0
  /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

(* A passive node i > 0 passes the token to node i-1. *)
PassToken(i) ==
  /\ ~ active[i]
  /\ token.pos = i
  /\ token' = [pos   |-> i - 1,
               q     |-> token.q + counter[i],
               color |-> IF color[i] = "black" THEN "black" ELSE token.color]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

(* An active node sends a message to some other node. *)
SendMsg(i) ==
  /\ active[i]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ \E j \in Node \ {i} : pending' = [pending EXCEPT ![j] = @ + 1]
  /\ UNCHANGED <<active, color, token>>

(* A node receives a message, becomes active and turns black. *)
RecvMsg(i) ==
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  /\ color'   = [color EXCEPT ![i] = "black"]
  /\ active'  = [active EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<token>>

(* An active node becomes passive. *)
Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, pending, token>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

---------------------------------------------------------------------------
(* Bounding the state space for model checking *)
MaxCounter == 3

StateConstraint ==
  /\ \A i \in Node : counter[i] <= MaxCounter /\ pending[i] <= MaxCounter
  /\ token.q <= MaxCounter

ActionConstraint ==
  \A i \in Node : counter'[i] <= MaxCounter /\ pending'[i] <= MaxCounter

---------------------------------------------------------------------------
(* Properties *)

terminated == \A i \in Node : ~ active[i] /\ pending[i] = 0

terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]
  /\ pending[0] = 0

TerminationDetection == terminationDetected => terminated

Liveness == terminated ~> terminationDetected

(* Number of messages in transit *)
B == SumF(pending, Node)

(* Inductive invariant capturing Safra's correctness argument *)
Inv ==
  /\ B = SumF(counter, Node)
  /\ \/ /\ \A i \in (token.pos + 1) .. (N - 1) : ~ active[i]
        /\ IF token.pos = N - 1
             THEN token.q = 0
             ELSE token.q = SumF(counter, (token.pos + 1) .. (N - 1))
     \/ SumF(counter, 0 .. token.pos) + token.q > 0
     \/ \E i \in 0 .. token.pos : color[i] = "black"
     \/ token.color = "black"

THEOREM Spec => [](TypeOK /\ Inv /\ TerminationDetection)
THEOREM Spec => Liveness
=============================================================================