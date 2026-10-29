------------------------------- MODULE EWD998 -------------------------------
EXTENDS Integers, Naturals, FiniteSets

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES active, color, counter, pending, token

vars == <<active, color, counter, pending, token>>

-----------------------------------------------------------------------------
(* Sum of f[x] over all x in S *)
RECURSIVE SumF(_, _)
SumF(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN  f[x] + SumF(f, S \ {x})

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
(* Node 0 initiates a new probe when the previous round was inconclusive. *)
InitiateProbe ==
  /\ token.pos = 0
  /\ \/ token.color = "black"
     \/ color[0] = "black"
     \/ counter[0] + token.q > 0
  /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

(* A passive node i # 0 holding the token passes it to node i-1. *)
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

-----------------------------------------------------------------------------
(* An active node sends a message to some other node. *)
SendMsg(i) ==
  /\ active[i]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ \E j \in Node \ {i} :
        pending' = [pending EXCEPT ![j] = @ + 1]
  /\ UNCHANGED <<active, color, token>>

(* A node receives a message, becomes active and black. *)
RecvMsg(i) ==
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  /\ active'  = [active EXCEPT ![i] = TRUE]
  /\ color'   = [color EXCEPT ![i] = "black"]
  /\ UNCHANGED <<token>>

(* An active node becomes passive. *)
Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, pending, token>>

Environment ==
  \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------
Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(* Bounds for model checking *)
MaxCounter == 3

StateConstraint ==
  /\ \A i \in Node : counter[i] <= MaxCounter /\ pending[i] <= MaxCounter
  /\ token.q <= MaxCounter * N

ActionConstraint ==
  \* Do not let the total number of in-flight messages exceed the bound.
  SumF(pending', Node) <= MaxCounter

-----------------------------------------------------------------------------
(* Properties *)
Termination ==
  \A i \in Node : ~ active[i] /\ pending[i] = 0

terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]
  /\ pending[0] = 0

TerminationDetection ==
  terminationDetected => Termination

Liveness ==
  Termination ~> terminationDetected

(* Inductive invariant capturing Safra's correctness argument *)
Inv ==
  /\ SumF(pending, Node) = SumF(counter, Node)
  /\ \/ /\ \A i \in (token.pos + 1) .. (N-1) : ~ active[i] /\ pending[i] = 0
        /\ IF token.pos = N-1
             THEN token.q = 0
             ELSE token.q = SumF(counter, (token.pos + 1) .. (N-1))
     \/ SumF(counter, 0 .. token.pos) + token.q > 0
     \/ \E i \in 0 .. token.pos : color[i] = "black"
     \/ token.color = "black"

THEOREM Spec => [](TypeOK /\ Inv /\ TerminationDetection)
THEOREM Spec => Liveness
=============================================================================