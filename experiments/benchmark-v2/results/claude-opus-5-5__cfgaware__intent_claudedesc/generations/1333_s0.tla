------------------------------- MODULE EWD998 -------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Nodes == 0 .. N-1
Color == {"white", "black"}

VARIABLES active, color, counter, pending, token

vars == <<active, color, counter, pending, token>>

-----------------------------------------------------------------------------

RECURSIVE SumF(_, _)
SumF(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + SumF(f, S \ {x})

Rng(a, b) == { i \in Nodes : a <= i /\ i <= b }

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
  /\ token \in [pos : Nodes, q : {0}, color : {"black"}]

-----------------------------------------------------------------------------
(* Token-related (system) actions *)

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
  /\ token' = [pos |-> i-1,
               q |-> token.q + counter[i],
               color |-> IF color[i] = "black" THEN "black" ELSE token.color]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

System == \/ InitiateProbe
          \/ \E i \in Nodes \ {0} : PassToken(i)

-----------------------------------------------------------------------------
(* Environment actions *)

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
(* Properties *)

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

B == SumF(pending, Nodes)

Inv ==
  /\ B = SumF(counter, Nodes)
  /\ \/ /\ \A i \in Rng(token.pos + 1, N-1) : active[i] = FALSE
        /\ token.q = SumF(counter, Rng(token.pos + 1, N-1))
     \/ SumF(counter, Rng(0, token.pos)) + token.q > 0
     \/ \E i \in Rng(0, token.pos) : color[i] = "black"
     \/ token.color = "black"

-----------------------------------------------------------------------------
(* Model-checking bounds *)

StateConstraint ==
  /\ \A i \in Nodes : counter[i] <= 3 /\ counter[i] >= -3 /\ pending[i] <= 3
  /\ token.q <= 9 /\ token.q >= -9

ActionConstraint ==
  \A i \in Nodes : pending'[i] <= 3

=============================================================================