---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLC

CONSTANT N
VARIABLES pc, flag, announced, inCS, waiting

Spec == 
  /\ pc \in [1..N -> {"start", "announce", "wait", "probe", "backoff", "cs", "release"}]
  /\ flag \in [1..N -> {0, 1}]
  /\ announced \in [1..N -> {0, 1}]
  /\ inCS \in [1..N -> {0, 1}]
  /\ waiting \in [1..N -> {0, 1}]

TypeInvariant == 
  /\ pc \in [1..N -> {"start", "announce", "wait", "probe", "backoff", "cs", "release"}]
  /\ flag \in [1..N -> {0, 1}]
  /\ announced \in [1..N -> {0, 1}]
  /\ inCS \in [1..N -> {0, 1}]
  /\ waiting \in [1..N -> {0, 1}]

Invariant == 
  /\ TypeInvariant
  /\ \A i \in 1..N : pc[i] = "cs" => inCS[i] = 1
  /\ \A i \in 1..N : pc[i] /= "cs" => inCS[i] = 0
  /\ \A i, j \in 1..N : i /= j => ~(pc[i] = "cs" /\ pc[j] = "cs")

Next(i \in 1..N) == 
  IF pc[i] = "start" THEN 
    /\ pc' = [pc EXCEPT ![i] = "announce"]
    /\ announced' = [announced EXCEPT ![i] = 1]
    /\ flag' = flag
    /\ inCS' = inCS
    /\ waiting' = waiting
  ELSE IF pc[i] = "announce" THEN 
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ announced' = announced
    /\ flag' = [flag EXCEPT ![i] = 1]
    /\ inCS' = inCS
    /\ waiting' = waiting
  ELSE IF pc[i] = "wait" THEN 
    /\ (/\ pc' = [pc EXCEPT ![i] = "probe"]
        /\ announced' = announced
        /\ flag' = flag
        /\ inCS' = inCS
        /\ waiting' = [waiting EXCEPT ![i] = 1])
    \/ (/\ pc' = [pc EXCEPT ![i] = "backoff"]
         /\ announced' = [announced EXCEPT ![i] = 0]
         /\ flag' = [flag EXCEPT ![i] = 0]
         /\ inCS' = inCS
         /\ waiting' = waiting)
  ELSE IF pc[i] = "probe" THEN 
    /\ (/\ pc' = [pc EXCEPT ![i] = "cs"]
         /\ announced' = announced
         /\ flag' = flag
         /\ inCS' = [inCS EXCEPT ![i] = 1]
         /\ waiting' = [waiting EXCEPT ![i] = 0])
    \/ (/\ pc' = [pc EXCEPT ![i] = "backoff"]
         /\ announced' = [announced EXCEPT ![i] = 0]
         /\ flag' = [flag EXCEPT ![i] = 0]
         /\ inCS' = inCS
         /\ waiting' = waiting)
  ELSE IF pc[i] = "cs" THEN 
    /\ pc' = [pc EXCEPT ![i] = "release"]
    /\ announced' = announced
    /\ flag' = flag
    /\ inCS' = inCS
    /\ waiting' = waiting
  ELSE IF pc[i] = "release" THEN 
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ announced' = [announced EXCEPT ![i] = 0]
    /\ flag' = [flag EXCEPT ![i] = 0]
    /\ inCS' = [inCS EXCEPT ![i] = 0]
    /\ waiting' = waiting
  ELSE 
    /\ pc' = pc
    /\ announced' = announced
    /\ flag' = flag
    /\ inCS' = inCS
    /\ waiting' = waiting

Next == \E i \in 1..N : Next(i)

Spec == Init /\ [][Next]_<<pc, flag, announced, inCS, waiting>>

M == 2

Liveness == 
  /\ \A i \in 1..N : WF_(Next(i))_(pc, flag, announced, inCS, waiting)
  /\ SF_(Next)_(pc, flag, announced, inCS, waiting)

THEOREM Spec => []Invariant
THEOREM Spec => Liveness
=============================================================================