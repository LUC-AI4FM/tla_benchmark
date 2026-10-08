```tla
 MODULE RingAlgorithm

EXTENDS Naturals, TLC, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, pc

Init == 
    /\ x = [i \in 1..N |-> 0]
    /\ y = [i \in 1..N |-> 0]
    /\ pc = [i \in 1..N |-> "start"]

Next ==
   \/ \E i \in 1..N : 
        (pc[i] = "start" 
         /\ x' = [x EXCEPT ![i] = 1]
         /\ y' = y
         /\ pc' = [pc EXCEPT ![i] = "copy"])
   \/ \E i \in 1..N :
        (pc[i] = "copy"
         /\ x' = x
         /\ y' = [y EXCEPT ![i] = x[If(i=1, N, i-1)]]
         /\ pc' = [pc EXCEPT ![i] = "done"])

Spec == 
   /\ Init
   /\ [][Next]_<<x,y,pc>>
   /\ WF_next(<<x,y,pc>>)

(* PlusCal algorithm in comments:
variables x, y \in [1..N -> 0];
variable pc \in [1..N -> "start"];
begin
    while \E i \in 1..N : pc[i] /= "done"
    do
        with (i)
        {
            if pc[i] = "start" then 
                x[i] := 1;
                pc[i] := "copy";
            else if pc[i] = "copy" then
                y[i] := x[(i-1)%N + 1];
                pc[i] := "done";
        }
    end while
end algorithm *)

Inv ==
   /\ \A i \in 1..N : pc[i] \in {"start", "copy", "done"}
   /\ \A i \in 1..N : x[i] \in {0, 1}
   /\ \A i \in 1..N : y[i] \in {0, 1}

Safety ==
    \A s \in States : 
        (\A i \in 1..N : pc[s][i] = "done") => 
        (\E j \in 1..N : y[s][j] = 1)

Liveness ==
   \/ \E t \in Nat : 
       (pc[t][1] = "done" /\ pc[t][2] = "done" /\ ... /\ pc[t][N] = "done")

TypeOK ==
    /\ x \in [1..N -> {0, 1}]
    /\ y \in [1..N -> {0, 1}]
    /\ pc \in [1..N -> {"start", "copy", "done"}]

THEOREM Spec => []Inv
<1>1. []
    BY <2> PCAL_PREFERS_INIT_THM DEF Init

THEOREM <<Spec, Liveness>> => Safety
<1>1. ASSUME NEW \A s \in States : (\A i \in 1..N : pc[s][i] = "done")
   <1>2. ASSERT \E j \in 1..N : y[NEW][j] = 1
      BY <3> DEF Safety, NEW

====

```