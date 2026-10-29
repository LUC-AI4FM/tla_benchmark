------------------------------- MODULE EWD998 -------------------------------
EXTENDS Integers, Naturals, FiniteSets

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Nodes == 0 .. N-1
Color == {"white", "black"}

VARIABLES
    active,
    color,
    counter,
    pending,
    token

vars == <<active, color, counter, pending, token>>

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ counter \in [Nodes -> Int]
    /\ pending \in [Nodes -> Nat]
    /\ token \in [pos : Nodes, q : Int, color : Color]

-----------------------------------------------------------------------------

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ counter = [i \in Nodes |-> 0]
    /\ pending = [i \in Nodes |-> 0]
    /\ token = [pos |-> 0, q |-> 0, color |-> "black"]

InitiateProbe ==
    /\ token.pos = 0
    /\ \/ token.color = "black"
       \/ color[0] = "black"
       \/ counter[0] + token.q > 0
    /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED <<active, counter, pending>>

PassToken(i) ==
    /\ ~active[i]
    /\ token.pos = i
    /\ token' = [pos   |-> i - 1,
                 q     |-> token.q + counter[i],
                 color |-> IF color[i] = "black" THEN "black" ELSE token.color]
    /\ color' = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED <<active, counter, pending>>

System ==
    \/ InitiateProbe
    \/ \E i \in Nodes \ {0} : PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i) ==
    /\ active[i]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ \E j \in Nodes \ {i} :
          pending' = [pending EXCEPT ![j] = @ + 1]
    /\ UNCHANGED <<active, color, token>>

RecvMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ color' = [color EXCEPT ![i] = "black"]
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<token>>

Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, counter, pending, token>>

Environment ==
    \E i \in Nodes : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

MaxCounter == 3
MaxPending == 2

StateConstraint ==
    \A i \in Nodes :
        /\ counter[i] <= MaxCounter
        /\ counter[i] >= -MaxCounter
        /\ pending[i] <= MaxPending
        /\ token.q <= MaxCounter
        /\ token.q >= -MaxCounter

ActionConstraint ==
    \* Bound the number of in-flight messages in successor states.
    \A i \in Nodes : pending'[i] <= MaxPending

-----------------------------------------------------------------------------

RECURSIVE SumS(_, _)
SumS(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + SumS(f, S \ {x})

B == SumS(pending, Nodes)

Rng(a, b) == {i \in Nodes : a <= i /\ i <= b}

Termination ==
    /\ \A i \in Nodes : ~active[i]
    /\ B = 0

terminationDetected ==
    /\ token.pos = 0
    /\ token.color = "white"
    /\ token.q + counter[0] = 0
    /\ color[0] = "white"
    /\ ~active[0]

TerminationDetection ==
    terminationDetected => Termination

Liveness ==
    Termination ~> terminationDetected

Inv ==
    /\ B = SumS(counter, Nodes)
    /\ \/ /\ \A i \in Rng(token.pos + 1, N - 1) : active[i] = FALSE
          /\ token.q = SumS(counter, Rng(token.pos + 1, N - 1))
       \/ SumS(counter, Rng(0, token.pos)) + token.q > 0
       \/ \E i \in Rng(0, token.pos) : color[i] = "black"
       \/ token.color = "black"

=============================================================================