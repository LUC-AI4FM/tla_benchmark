---------------------------- MODULE InnerModule ----------------------------
EXTENDS Integers

VARIABLE result
VARIABLE seq

InnerStep == result = 0 /\ result' = 1 /\ seq' = SelectSeq(seq, lambda x : x # 1)

Inner == InnerStep \/ (result = 1 /\ UNCHANGED <<result, seq>>)

==================================