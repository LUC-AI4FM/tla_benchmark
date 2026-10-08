```
------------------------------ MODULE Inner725f ------------------------------
VARIABLES res, myseq

Init == /\ res = 0
      /\ myseq = <<1,2,3>>

Step == /\ res = 0
       /\ res' = 1
       /\ myseq' = << y \in myseq : y # res' >>

Next == Step \/ (res' = res /\ myseq' = myseq)

------------------------------ MODULE Outer725f ------------------------------
EXTENDS Temporal

VARIABLES outerRes, outerSeq

vars == {outerRes, outerSeq}

INSTANCE Inner725f AS Svc WITH res = outerRes, myseq = outerSeq

Spec == Svc.Init /\ [][Svc.Next]_vars /\ WF_vars(Svc.Step)

SpecRunsToEnd == <>[] (outerRes # 0)
```