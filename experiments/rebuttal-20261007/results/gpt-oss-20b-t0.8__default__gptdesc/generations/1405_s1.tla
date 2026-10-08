MODULE InnerModule
EXTENDS Sequences, SetTheory

VARIABLES result, seq

SelectSeq(s, p) == {x \in s : p(x)}

Step ==
  /\ result = 0
  /\ result' = 1
  /\ seq' = SelectSeq(seq, \lambda x : x # 1)

===============================================================================

MODULE OuterSpec
EXTENDS Sequences, SetTheory

CONSTANTS initialSeq

VARIABLES r, s

INSTANCE InnerModule AS Inn WITH
  result = r,
  seq = s

Init == /\ r = 0
       /\ s = initialSeq

stutter == UNCHANGED <<r,s>>

Next == \/ Step
        \/ stutter

Liveliness == <> [] ~ENABLED(Step)

Spec == Init
       /\ [][Next]_(<<r,s>>)
       /\ WF_<<r,s>>[Step]
       /\ Liveliness

===============================================================================