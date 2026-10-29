---------------------------- MODULE EWD998 ----------------------------
EXTENDS Integers, FiniteSets, Naturals, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

ASSUME TLCSet(1, 0) /\ TLCSet(2, 0)

Nodes == 0 .. N-1
Color == {"white", "black"}

VARIABLES
  active,
  color,
  counter,
  pending,
  token

vars == <<active, color, counter, pending, token>>

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
  /\ ~ active[i]
  /\ token.pos = i
  /\ token' = [pos |-> i-1, q |-> token.q + counter[i],
               color |-> IF color[i] = "black" THEN "black" ELSE token.color]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

System == InitiateProbe \/ \E i \in Nodes \ {0} : PassToken(i)

SendMsg(i) ==
  /\ active[i]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ \E j \in Nodes \ {i} : pending' = [pending EXCEPT ![j] = @ + 1]
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

Environment == \E i \in Nodes : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

StateConstraint ==
  /\ \A i \in Nodes : counter[i] <= 3 /\ pending[i] <= 3
  /\ token.q <= 9

ActionConstraint ==
  /\ (token'.pos # token.pos /\ token.pos # 0) => TLCSet(1, TLCGet(1) + 1)
  /\ (\E i \in Nodes : ~ active[i] /\ active'[i]) => TLCSet(2, TLCGet(2) + 1)

RECURSIVE SumF(_, _)
SumF(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + SumF(f, S \ {x})

Rng(a, b) == {i \in Nodes : a <= i /\ i <= b}

terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

Termination ==
  \A i \in Nodes : ~ active[i] /\ pending[i] = 0

TerminationDetection == terminationDetected => Termination

Liveness == Termination ~> terminationDetected

Inv ==
  /\ SumF(pending, Nodes) = SumF(counter, Nodes)
  /\ \/ /\ \A i \in Rng(token.pos + 1, N-1) : active[i] = FALSE
        /\ IF token.pos = N-1
             THEN token.q = 0
             ELSE token.q = SumF(counter, Rng(token.pos + 1, N-1))
     \/ SumF(counter, Rng(0, token.pos)) + token.q > 0
     \/ \E i \in Rng(0, token.pos) : color[i] = "black"
     \/ token.color = "black"

Alias ==
  [ active      |-> active,
    color       |-> color,
    counter     |-> counter,
    pending     |-> pending,
    token       |-> token,
    tokenPasses |-> TLCGet(1),
    activations |-> TLCGet(2),
    tokenStats  |-> [pos |-> token.pos, q |-> token.q, color |-> token.color,
                     level |-> TLCGet("level")] ]

=============================================================================