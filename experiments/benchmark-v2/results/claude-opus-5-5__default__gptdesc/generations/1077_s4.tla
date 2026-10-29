---------------------------- MODULE EWD998PCal ----------------------------
EXTENDS Integers, FiniteSets, Bags, TLC

----------------------------- MODULE EWD998 -----------------------------
(***************************************************************************)
(* Abstract specification of Safra's termination detection algorithm      *)
(* (EWD 998). The token is modeled as a record with position, counter q,   *)
(* and color.                                                              *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLES active, color, counter, pending, token

Node == 0 .. N-1
Color == {"white", "black"}

vars == <<active, color, counter, pending, token>>

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN  f[x] + SumOver(f, S \ {x})

Rng(a, b) == { i \in Node : a <= i /\ i <= b }

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ pending \in [Node -> Nat]
  /\ token \in [pos : Node, q : Int, color : Color]

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter = [i \in Node |-> 0]
  /\ pending = [i \in Node |-> 0]
  /\ token \in [pos : Node, q : {0}, color : {"black"}]

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

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

SendMsg(i) ==
  /\ active[i]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ \E j \in Node \ {i} : pending' = [pending EXCEPT ![j] = @ + 1]
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

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

terminated ==
  \A i \in Node : ~ active[i] /\ pending[i] = 0

terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

Inv ==
  /\ SumOver(pending, Node) = SumOver(counter, Node)
  /\ \/ /\ \A i \in Rng(token.pos + 1, N-1) : active[i] = FALSE
        /\ token.q = SumOver(counter, Rng(token.pos + 1, N-1))
     \/ SumOver(counter, Rng(0, token.pos)) + token.q > 0
     \/ \E i \in Rng(0, token.pos) : color[i] = "black"
     \/ token.color = "black"

Termination == terminationDetected => terminated

Liveness == terminated ~> terminationDetected
=============================================================================