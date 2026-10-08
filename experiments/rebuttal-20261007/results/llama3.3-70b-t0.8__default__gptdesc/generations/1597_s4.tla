```
MODULE LamportFastMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, b, pc1, pc2, failed1, failed2

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = FALSE
  /\ pc1 = "noncrit"
  /\ pc2 = "noncrit"
  /\ failed1 = FALSE
  /\ failed2 = [i \in 2..N |-> FALSE]

Next ==
  \/ (pc1 = "noncrit" /\ x = 0 /\ y = 0 /\ b = FALSE
      /\ pc1' = "trying"
      /\ x' = 1
      /\ y' = 0
      /\ b' = FALSE
      /\ UNCHANGED <<pc2, failed1, failed2>>)
  \/ (pc1 = "trying" /\ x = 1 /\ y = 0 /\ b = FALSE
      /\ pc1' = "crit"
      /\ x' = 1
      /\ y' = 1
      /\ b' = TRUE
      /\ UNCHANGED <<pc2, failed1, failed2>>)
  \/ (pc1 = "crit" /\ x = 1 /\ y = 1 /\ b = TRUE
      /\ pc1' = "exit"
      /\ x' = 1
      /\ y' = 0
      /\ b' = FALSE
      /\ UNCHANGED <<pc2, failed1, failed2>>)
  \/ (pc1 = "exit" /\ x = 1 /\ y = 0 /\ b = FALSE
      /\ pc1' = "noncrit"
      /\ x' = 0
      /\ y' = 0
      /\ b' = FALSE
      /\ UNCHANGED <<pc2, failed1, failed2>>)
  \/ \E i \in 2..N :
        (pc2[i] = "noncrit" /\ x = 0 /\ y = 0 /\ b = FALSE
         /\ pc2' = [j \in 2..N |-> IF j = i THEN "trying" ELSE pc2[j]]
         /\ x' = 0
         /\ y' = 0
         /\ b' = FALSE
         /\ failed2' = [j \in 2..N |-> IF j = i THEN TRUE ELSE failed2[j]]
         /\ UNCHANGED <<pc1, failed1>>)
  \/ \E i \in 2..N :
        (pc2[i] = "trying" /\ x = 0 /\ y = 0 /\ b = FALSE
         /\ pc2' = [j \in 2..N |-> IF j = i THEN "crit" ELSE pc2[j]]
         /\ x' = 0
         /\ y' = 1
         /\ b' = TRUE
         /\ failed2' = [j \in 2..N |-> IF j = i THEN FALSE ELSE failed2[j]]
         /\ UNCHANGED <<pc1, failed1>>)
  \/ \E i \in 2..N :
        (pc2[i] = "crit" /\ x = 0 /\ y = 1 /\ b = TRUE
         /\ pc2' = [j \in 2..N |-> IF j = i THEN "exit" ELSE pc2[j]]
         /\ x' = 0
         /\ y' = 0
         /\ b' = FALSE
         /\ failed2' = [j \in 2..N |-> IF j = i THEN TRUE ELSE failed2[j]]
         /\ UNCHANGED <<pc1, failed1>>)
  \/ \E i \in 2..N :
        (pc2[i] = "exit" /\ x = 0 /\ y = 0 /\ b = FALSE
         /\ pc2' = [j \in 2..N |-> IF j = i THEN "noncrit" ELSE pc2[j]]
         /\ x' = 0
         /\ y' = 0
         /\ b' = FALSE
         /\ failed2' = [j \in 2..N |-> IF j = i THEN FALSE ELSE failed2[j]]
         /\ UNCHANGED <<pc1, failed1>>)

Spec ==
  /\ Init
  /\ [][Next]_<<x, y, b, pc1, pc2, failed1, failed2>>
  /\ WF_vars(Next, <<pc1, pc2, failed1, failed2>>)
  /\ \A i \in 2..N : SF_vars(Next, <<pc1, pc2[i], failed1, failed2[i]]>)
  /\ MutualExclusion
  /\ Liveness

MutualExclusion ==
  \A i, j \in (1 .. N) :
    ~ (pc1 = "crit" /\ pc2[j] = "crit")

Liveness ==
  <>[]<>(\E i \in (1 .. N) : (pc1 = "crit" \/ pc2[i] = "crit"))
```