```tla
MODULE FastMutex
EXTENDS Integers, FiniteSets, TLC

CONSTANTS M, N
VARIABLES x, y, b, cs

Init == /\ x = 0 
        /\ y = 0 
        /\ b = <<FALSE, FALSE>>
        /\ cs = {}

Next == \/ \E i \in 1..M : (x = 0) -> [][x' = i]_<<x,y,b,cs>> 
          \/ \E j \in (M+1)..N : (y = 0) -> [][y' = j]_<<x,y,b,cs>>
          \/ \E i \in 1..M : /\ x = i
                                /\ b[2] = FALSE
                                /\ y # i
                                -> [][b' = <<TRUE, b[2]>>, cs' = {i}]_<<x,y,b,cs>>
          \/ \E j \in (M+1)..N : /\ y = j
                                 /\ b[1] = FALSE
                                 /\ x # j
                                 -> [][b' = <<b[1], TRUE>>, cs' = {j}]_<<x,y,b,cs>>
          \/ \E i \in 1..M : /\ b = <<TRUE, FALSE>>
                                /\ y # i
                                -> [][b' = <<FALSE, b[2]>>, x' = 0, cs' = {}]_<<x,y,b,cs>>
          \/ \E j \in (M+1)..N : /\ b = <<FALSE, TRUE>>
                                 /\ x # j
                                 -> [][b' = <<b[1], FALSE>>, y' = 0, cs' = {}]_<<x,y,b,cs>>

Spec == Init /\ [][Next]_<<x,y,b,cs>> /\ WF_<<x>>_Process1 /\ SF_<<y>>_Process2

MutualExclusion == \/ cs = {}
                     \/ \E p \in cs : \A q \in cs \ {p} : q \notin cs

Liveness == []<> (\E i \in 1..N : i \in cs)

TemporalSpec == Spec /\ <>[] MutualExclusion /\ Liveness
```