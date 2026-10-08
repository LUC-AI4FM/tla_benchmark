MODULE MutualExclusion(N)

EXTENDS Naturals

CONSTANT N

VARIABLES inCS, flag, fastDoorway

vars == <<inCS, flag, fastDoorway>>

TypeInvariant ==
   /\ inCS ∈ [1..N -> BOOLEAN]
   /\ flag ∈ [1..N -> BOOLEAN]
   /\ fastDoorway ∈ BOOLEAN

Init ==
   /\ inCS = [i \in 1..N |-> FALSE]
   /\ flag = [i \in 1..N |-> FALSE]
   /\ fastDoorway = FALSE
   /\ TypeInvariant

SetIntent(i) ==
   /\ i ∈ 1..N
   /\ flag[i] = FALSE
   /\ inCS[i] = FALSE
   /\ flag' = [flag EXCEPT ![i] = TRUE]
   /\ UNCHANGED <<fastDoorway, inCS>>

FastEnter(i) ==
   /\ i ∈ 1..N
   /\ NOT fastDoorway
   /\ flag[i] = TRUE
   /\ inCS[i] = FALSE
   /\ fastDoorway' = TRUE
   /\ inCS'[i] = TRUE
   /\ UNCHANGED <<flag>>

WithdrawFast(i) ==
   /\ i ∈ 1..N
   /\ fastDoorway
   /\ flag[i] = TRUE
   /\ inCS[i] = FALSE
   /\ flag'[i] = FALSE
   /\ UNCHANGED <<fastDoorway, inCS>>

BackupWait(i) ==
   /\ i ∈ 1..N
   /\ flag[i] = TRUE
   /\ fastDoorway = FALSE
   /\ ∀ j \in 1..(i-1) : flag[j] = FALSE
   /\ inCS'[i] = TRUE
   /\ flag' = [flag EXCEPT ![i] = FALSE]
   /\ UNCHANGED <<fastDoorway>>

Exit(i) ==
   /\ i ∈ 1..N
   /\ inCS[i] = TRUE
   /\ inCS'[i] = FALSE
   /\ fastDoorway' = FALSE
   /\ flag'[i] = FALSE

Next ==
   ∨ i \in 1..N :
      SetIntent(i) \/ FastEnter(i) \/ WithdrawFast(i) \/ BackupWait(i) \/ Exit(i)

MutualExclusion == ONE i \in 1..N : inCS[i]

Spec == Init /\ []TypeInvariant /\ [][Next]_vars /\ WF_vars(Next)

THEOREM MutualExclusionInv == Spec => []MutualExclusion

THEOREM ProgressLiveness == Spec => <>∃ i ∈ 1..N : inCS[i]