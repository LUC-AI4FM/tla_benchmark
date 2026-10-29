--------------------------- MODULE EWD998PCal ---------------------------
(***************************************************************************)
(* Safra's distributed termination detection algorithm on a ring of N     *)
(* nodes (EWD 998), modelled in PlusCal with a bag-based message network  *)
(* that carries payload messages and a circulating token with fields q    *)
(* and color.                                                             *)
(***************************************************************************)
EXTENDS Integers, Bags, TLC

(***************************************************************************)
(* The high-level specification EWD998. It is given here as an inner      *)
(* module so that the refinement-style comparison by INSTANCE is          *)
(* self-contained.                                                        *)
(***************************************************************************)
------------------------------ MODULE EWD998 ------------------------------
CONSTANT N

VARIABLES active, color, counter, pending, token

Node  == 0 .. N-1
Color == {"white", "black"}

hvars == << active, color, counter, pending, token >>

TypeOK ==
  /\ active  \in [Node -> BOOLEAN]
  /\ color   \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ pending \in [Node -> Nat]
  /\ token   \in [pos : Node, q : Int, color : Color]

Init ==
  /\ active  \in [Node -> BOOLEAN]
  /\ color   = [i \in Node |-> "black"]
  /\ counter = [i \in Node |-> 0]
  /\ pending = [i \in Node |-> 0]
  /\ token   = [pos |-> 0, q |-> 0, color |-> "black"]

InitiateProbe ==
  /\ token.pos = 0
  /\ \/ token.color = "black"
     \/ color[0] = "black"
     \/ counter[0] + token.q # 0
  /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED << active, counter, pending >>

PassToken(i) ==
  /\ i # 0
  /\ ~ active[i]
  /\ token.pos = i
  /\ token' = [pos   |-> i-1,
               q     |-> token.q + counter[i],
               color |-> IF color[i] = "black" THEN "black" ELSE token.color]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED << active, counter, pending >>

SendMsg(i) ==
  /\ active[i]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ \E j \in Node \ {i} :
        pending' = [pending EXCEPT ![j] = @ + 1]
  /\ UNCHANGED << active, color, token >>

RecvMsg(i) ==
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  /\ color'   = [color EXCEPT ![i] = "black"]
  /\ active'  = [active EXCEPT ![i] = TRUE]
  /\ UNCHANGED token

Deactivate(i) ==
  /\ active'  = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED << color, counter, pending, token >>

System      == InitiateProbe \/ \E i \in Node : PassToken(i)
Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_hvars /\ WF_hvars(System)

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE x \in S : TRUE
                  IN  f[x] + Sum(f, S \ {x})

Rng(a, b) == { i \in Node : a <= i /\ i <= b }

Termination ==
  \A i \in Node : ~ active[i] /\ pending[i] = 0

terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

Inv ==
  /\ Sum(pending, Node) = Sum(counter, Node)
  /\ \/ /\ \A i \in Rng(token.pos + 1, N-1) : active[i] = FALSE
        /\ IF token.pos = N-1
             THEN token.q = 0
             ELSE token.q = Sum(counter, Rng(token.pos + 1, N-1))
     \/ Sum(counter, Rng(0, token.pos)) + token.q > 0
     \/ \E i \in Rng(0, token.pos) : color[i] = "black"
     \/ token.color = "black"

TerminationDetection == terminationDetected => Termination

Liveness == Termination ~> terminationDetected
===========================================================================