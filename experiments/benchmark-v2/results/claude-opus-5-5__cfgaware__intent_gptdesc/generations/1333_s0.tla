---- MODULE EWD998Safra ----
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Nodes == 0 .. N-1

Color == {"white", "black"}

Initiator == 0

\* Bounds used only to keep the state space finite during model checking.
MaxCounter == 3
MaxPending == 3

VARIABLES
  active,   \* active[i] : is node i active?
  color,    \* color[i]  : color of node i
  counter,  \* counter[i]: #msgs sent - #msgs received by node i
  pending,  \* pending[i]: #messages in transit to node i
  token     \* the circulating token [pos, q, color]

vars == <<active, color, counter, pending, token>>

----------------------------------------------------------------------------
\* Helpers

RECURSIVE SumS(_, _)
SumS(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumS(f, S \ {x})

Rng(a, b) == {i \in Nodes : a <= i /\ i <= b}

----------------------------------------------------------------------------

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ counter \in [Nodes -> Int]
  /\ pending \in [Nodes -> Nat]
  /\ token \in [pos : Nodes, q : Int, color : Color]

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ counter = [i \in Nodes |-> 0]
  /\ pending = [i \in Nodes |-> 0]
  /\ token = [pos |-> Initiator, q |-> 0, color |-> "black"]

----------------------------------------------------------------------------
\* Algorithm (System) actions

InitiateProbe ==
  /\ token.pos = Initiator
  /\ \/ token.color = "black"
     \/ color[Initiator] = "black"
     \/ counter[Initiator] + token.q # 0
  /\ token' = [pos |-> N - 1, q |-> 0, color |-> "white"]
  /\ color' = [color EXCEPT ![Initiator] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

PassToken(i) ==
  /\ i # Initiator
  /\ ~active[i]
  /\ token.pos = i
  /\ token' = [pos   |-> i - 1,
               q     |-> token.q + counter[i],
               color |-> IF color[i] = "black" THEN "black" ELSE token.color]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

System == InitiateProbe \/ \E i \in Nodes \ {Initiator} : PassToken(i)

----------------------------------------------------------------------------
\* Environment (application) actions

SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Nodes \ {i} :
       pending' = [pending EXCEPT ![j] = @ + 1]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ UNCHANGED <<active, color, token>>

RecvMsg(i) ==
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  /\ color' = [color EXCEPT ![i] = "black"]
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ UNCHANGED token

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, pending, token>>

Environment ==
  \E i \in Nodes : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

----------------------------------------------------------------------------

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

----------------------------------------------------------------------------
\* Properties

Terminated ==
  \A i \in Nodes : ~active[i] /\ pending[i] = 0

TerminationDetected ==
  /\ token.pos = Initiator
  /\ token.color = "white"
  /\ token.q + counter[Initiator] = 0
  /\ color[Initiator] = "white"
  /\ ~active[Initiator]

\* Safety: detection soundness
Safe == TerminationDetected => Terminated

\* Safra's inductive invariant
Inv ==
  /\ SumS(pending, Nodes) = SumS(counter, Nodes)
  /\ \/ /\ \A i \in Rng(token.pos + 1, N - 1) : ~active[i]
        /\ token.q = SumS(counter, Rng(token.pos + 1, N - 1))
     \/ SumS(counter, Rng(0, token.pos)) + token.q > 0
     \/ \E i \in Rng(0, token.pos) : color[i] = "black"
     \/ token.color = "black"

\* Liveness: termination is eventually detected
Liveness == Terminated ~> TerminationDetected

----------------------------------------------------------------------------
\* Model-checking bounds

StateConstraint ==
  /\ \A i \in Nodes : counter[i] <= MaxCounter /\ counter[i] >= -MaxCounter
  /\ \A i \in Nodes : pending[i] <= MaxPending
  /\ token.q <= MaxCounter * N /\ token.q >= -(MaxCounter * N)

ActionConstraint ==
  /\ \A i \in Nodes : counter'[i] <= MaxCounter
  /\ \A i \in Nodes : pending'[i] <= MaxPending

====