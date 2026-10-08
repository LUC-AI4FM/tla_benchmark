MODULE GraphBoundedSeqHelpers
EXTENDS Naturals, TLC

CONSTANTS V, E

(* Helper operators *)

BoundedSeq(n) == { i \in 1..n }

SeqFromSet(S) ==
  [ i \in 1..#S |-> CHOOSE x \in S : True ]

TestGraph == { e \in E | e[1] # e[2] }      (* edges with distinct vertices *)

CardCheck == TLCEval(#TestGraph) = #V * (#V - 1)

BSeq == 1..3

NestedSeq == { i | i \in 1..#BSeq }

AssumeCardinalityInv == TLCEval(#NestedSeq)=3

VARIABLES var1, var2

Init ==
  /\ var1 = TLCEval(RandomElement(SeqFromSet(TestGraph)))
  /\ var2 = TLCEval(RandomElement(SeqFromSet(TestGraph)))

Next ==
  \/ /\ var1' = TLCEval(RandomElement(SeqFromSet(TestGraph)))
     /\ var2' = var2
  \/ /\ var1' = var1
     /\ var2' = TLCEval(RandomElement(SeqFromSet(TestGraph)))

Inv == (var1 \in TestGraph) /\ (var2 \in TestGraph) /\ CardCheck /\ AssumeCardinalityInv

Spec == Init /\ [][Next]_<<var1,var2>> /\ Inv