------------------------------- MODULE EWD998 -------------------------------
(***************************************************************************)
(* Safra's termination detection algorithm for a ring of N nodes          *)
(* (EWD 998).                                                              *)
(***************************************************************************)
EXTENDS Integers, Naturals, FiniteSets

CONSTANTS N

ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES
    active,   \* active[i] : is node i active?
    color,    \* color[i]  : color of node i
    counter,  \* counter[i]: messages sent minus messages received at node i
    pending,  \* pending[i]: number of messages in transit to node i
    token     \* the token: [pos, q, color]

vars == <<active, color, counter, pending, token>>

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
    /\ token   \in [pos : Node, q : {0}, color : {"black"}]

-----------------------------------------------------------------------------
(* System actions: token handling                                          *)

\* Node 0 initiates a new probe when the previous one was unsuccessful.
InitiateProbe ==
    /\ token.pos = 0
    /\ \/ token.color = "black"
       \/ color[0] = "black"
       \/ counter[0] + token.q > 0
    /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED <<active, counter, pending>>

\* A passive node i (other than 0) holding the token passes it on.
PassToken(i) ==
    /\ i # 0
    /\ ~ active[i]
    /\ token.pos = i
    /\ token' = [pos   |-> i - 1,
                 q     |-> token.q + counter[i],
                 color |-> IF color[i] = "black" THEN "black" ELSE token.color]
    /\ color' = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED <<active, counter, pending>>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------
(* Environment actions: the underlying computation                         *)

\* An active node i sends a message to some other node j.
SendMsg(i) ==
    /\ active[i]
    /\ \E j \in Node \ {i} :
          pending' = [pending EXCEPT ![j] = @ + 1]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ UNCHANGED <<active, color, token>>

\* Node i receives a message: it becomes active and black.
RecvMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ color'   = [color EXCEPT ![i] = "black"]
    /\ active'  = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<token>>

\* An active node becomes passive.
Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, counter, pending, token>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(* Model-checking constraints                                              *)

MaxCounter == 3

StateConstraint ==
    /\ \A i \in Node : counter[i] <= MaxCounter /\ pending[i] <= MaxCounter
    /\ token.q <= MaxCounter * N
    /\ token.q >= -(MaxCounter * N)

ActionConstraint ==
    \A i \in Node : counter'[i] <= MaxCounter /\ pending'[i] <= MaxCounter

-----------------------------------------------------------------------------
(* Properties                                                              *)

RECURSIVE SumF(_, _)
SumF(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  f[x] + SumF(f, S \ {x})

Rng(a, b) == {i \in Node : a <= i /\ i <= b}

terminated ==
    \A i \in Node : ~ active[i] /\ pending[i] = 0

terminationDetected ==
    /\ token.pos = 0
    /\ token.color = "white"
    /\ token.q + counter[0] = 0
    /\ color[0] = "white"
    /\ ~ active[0]

\* Safety: termination is only detected when the system has terminated.
TerminationDetection == terminationDetected => terminated

\* Liveness: termination is eventually detected.
Liveness == terminated ~> terminationDetected

\* Termination is stable.
TerminatedStable == [][terminated => terminated']_vars

\* Safra's inductive invariant.
Inv ==
    /\ SumF(pending, Node) = SumF(counter, Node)
    /\ \/ /\ \A i \in Rng(token.pos + 1, N - 1) : ~ active[i]
          /\ token.q = SumF(counter, Rng(token.pos + 1, N - 1))
       \/ SumF(counter, Rng(0, token.pos)) + token.q > 0
       \/ \E i \in Rng(0, token.pos) : color[i] = "black"
       \/ token.color = "black"

IndInv == TypeOK /\ Inv

THEOREM Spec => [](TypeOK /\ Inv /\ TerminationDetection)
THEOREM Spec => Liveness
=============================================================================