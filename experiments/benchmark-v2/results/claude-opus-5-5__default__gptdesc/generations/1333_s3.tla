------------------------------- MODULE EWD998 -------------------------------
(***************************************************************************)
(* TLA+ specification of Safra's algorithm for distributed termination     *)
(* detection on a ring, as described in EWD 998.                           *)
(***************************************************************************)
EXTENDS Integers, Naturals, FiniteSets

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES
  active,   \* activation status of nodes
  color,    \* color of nodes
  counter,  \* nb of sent messages - nb of received messages per node
  pending,  \* nb of messages in transit to each node
  token     \* token: position, counter, color

vars == <<active, color, counter, pending, token>>

-----------------------------------------------------------------------------
(* Sum of f[x] for x in S *)
RECURSIVE SumF(_, _)
SumF(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN  f[x] + SumF(f, S \ {x})

TypeOK ==
  /\ active  \in [Node -> BOOLEAN]
  /\ color   \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ pending \in [Node -> Nat]
  /\ token   \in [pos : Node, q : Int, color : Color]

-----------------------------------------------------------------------------
Init ==
  /\ active  \in [Node -> BOOLEAN]
  /\ color   \in [Node -> Color]
  /\ counter = [i \in Node |-> 0]
  /\ pending = [i \in Node |-> 0]
  /\ token   = [pos |-> 0, q |-> 0, color |-> "black"]

(* Node 0 initiates a new probe if the previous one was unsuccessful. *)
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

System ==
  \/ InitiateProbe
  \/ \E i \in Node \ {0} : PassToken(i)

(* An active node i sends a message to some other node j. *)
SendMsg(i) ==
  /\ active[i]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ \E j \in Node \ {i} :
        pending' = [pending EXCEPT ![j] = @ + 1]
  /\ UNCHANGED <<active, color, token>>

(* Node i receives a message, becomes active and black. *)
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

Environment ==
  \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(* Bounds for model checking *)
MaxCount == 3

StateConstraint ==
  /\ \A i \in Node : counter[i] <= MaxCount /\ pending[i] <= MaxCount
  /\ token.q <= MaxCount

ActionConstraint ==
  \* Bound the total number of messages in transit after each step.
  SumF(pending', Node) <= MaxCount

-----------------------------------------------------------------------------
(* Correctness properties *)

\* Number of messages in transit
B == SumF(pending, Node)

\* System has terminated: all nodes passive and no messages in transit
Termination ==
  /\ \A i \in Node : ~ active[i]
  /\ B = 0

\* Node 0 detects termination
terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

\* Safety: termination is detected only if the system has terminated
TerminationDetection == terminationDetected => Termination

\* Liveness: termination is eventually detected
Liveness == Termination ~> terminationDetected

\* Counter invariant: sum of counters equals messages in transit
CounterInv == B = SumF(counter, Node)

-----------------------------------------------------------------------------
(* Safra's inductive invariant *)
Rng(a, b) == {i \in Node : a <= i /\ i <= b}

Inv ==
  /\ B = SumF(counter, Node)
  /\ \/ /\ \A i \in Rng(token.pos + 1, N - 1) : ~ active[i]
        /\ IF token.pos = N - 1
              THEN token.q = 0
              ELSE token.q = SumF(counter, Rng(token.pos + 1, N - 1))
     \/ SumF(counter, Rng(0, token.pos)) + token.q > 0
     \/ \E i \in Rng(0, token.pos) : color[i] = "black"
     \/ token.color = "black"

IndInv == TypeOK /\ Inv

THEOREM Spec => [](TypeOK /\ Inv /\ TerminationDetection)
THEOREM Spec => Liveness
=============================================================================