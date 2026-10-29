------------------------------- MODULE SafraTermination -------------------------------
(***************************************************************************)
(* Safra's algorithm (EWD 998) for termination detection on a ring.         *)
(* Nodes 0..N-1 form a ring. The token travels from node i to node i-1.    *)
(* Node 0 is the initiator: it starts probes and declares termination.     *)
(***************************************************************************)
EXTENDS Naturals, Integers

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

\* Ring structure: the token moves from Successor-side to Predecessor-side
Predecessor(i) == IF i = 0 THEN N-1 ELSE i-1
Successor(i)   == IF i = N-1 THEN 0 ELSE i+1

VARIABLES
  active,   \* active[i]: node i is active
  color,    \* color[i]: node i has received a message since it last passed the token
  counter,  \* counter[i]: messages sent minus messages received by node i
  pending,  \* pending[i]: number of messages in transit to node i
  token     \* the token: position, accumulated count q, and color

vars == <<active, color, counter, pending, token>>

TokenType == [pos : Node, q : Int, color : Color]

TypeOK ==
  /\ active  \in [Node -> BOOLEAN]
  /\ color   \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ pending \in [Node -> Nat]
  /\ token   \in TokenType

---------------------------------------------------------------------------
Init ==
  /\ active  \in [Node -> BOOLEAN]
  /\ color   \in [Node -> Color]
  /\ counter = [i \in Node |-> 0]
  /\ pending = [i \in Node |-> 0]
  /\ token   = [pos |-> 0, q |-> 0, color |-> "black"]

---------------------------------------------------------------------------
(* Token-related actions *)

\* Node 0 initiates a new probe when the previous round was inconclusive.
InitiateProbe ==
  /\ token.pos = 0
  /\ \/ token.color = "black"
     \/ color[0] = "black"
     \/ counter[0] + token.q # 0
  /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

\* An inactive node i # 0 holding the token passes it to its predecessor.
PassToken(i) ==
  /\ i # 0
  /\ ~ active[i]
  /\ token.pos = i
  /\ token' = [pos   |-> Predecessor(i),
               q     |-> token.q + counter[i],
               color |-> IF color[i] = "black" THEN "black" ELSE token.color]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

---------------------------------------------------------------------------
(* Environment (underlying computation) actions *)

SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Node \ {i} :
        /\ pending' = [pending EXCEPT ![j] = @ + 1]
        /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ UNCHANGED <<active, color, token>>

RecvMsg(i) ==
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  /\ active'  = [active EXCEPT ![i] = TRUE]
  /\ color'   = [color EXCEPT ![i] = "black"]
  /\ UNCHANGED token

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, pending, token>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

---------------------------------------------------------------------------
Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

---------------------------------------------------------------------------
(* Properties *)

\* Actual global termination: all nodes inactive, no messages in transit
Termination ==
  \A i \in Node : ~ active[i] /\ pending[i] = 0

\* Termination as detected by the initiator
terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

\* Safety: no false positives
TDCorrect == terminationDetected => Termination

\* Termination is stable once reached
TerminationStable == [][Termination => Termination']_vars

\* Liveness: termination is eventually detected
Liveness == Termination ~> terminationDetected

\* Safra's inductive invariant (for reference / checking)
Sum(f, S) ==
  LET RECURSIVE SumRec(_)
      SumRec(T) == IF T = {} THEN 0
                   ELSE LET x == CHOOSE x \in T : TRUE
                        IN f[x] + SumRec(T \ {x})
  IN SumRec(S)

Rng(a, b) == {k \in Node : a <= k /\ k <= b}

Inv ==
  /\ Sum(pending, Node) = Sum(counter, Node)
  /\ \/ /\ \A i \in Rng(token.pos + 1, N-1) : ~ active[i]
        /\ token.q = Sum(counter, Rng(token.pos + 1, N-1))
     \/ Sum(counter, Rng(0, token.pos)) + token.q > 0
     \/ \E i \in Rng(0, token.pos) : color[i] = "black"
     \/ token.color = "black"

THEOREM Spec => [](TypeOK /\ TDCorrect)
THEOREM Spec => Liveness
=========================================================================================