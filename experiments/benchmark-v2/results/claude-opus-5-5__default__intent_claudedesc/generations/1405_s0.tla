------------------------------- MODULE SelectSeqInstance -------------------------------
EXTENDS Sequences, Naturals

VARIABLES seq, res

vars == <<seq, res>>

---------------------------------- MODULE Inner ----------------------------------
EXTENDS Sequences, Naturals

VARIABLES s, x

Step == /\ x = 0
        /\ x' = 1
        /\ s' = SelectSeq(s, LAMBDA e : e # x')
====================================================================================