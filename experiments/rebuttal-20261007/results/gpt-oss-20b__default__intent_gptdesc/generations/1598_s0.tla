------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N
ASSUME N > 0

VARIABLES flags, reg1, reg2, state

Init ==
    /\ flags = [i \in 1..N |-> FALSE]
    /\ reg1 = 0
    /\ reg2 = 0
    /\ state = [i \in 1..N |-> "Idle"]

SetIntent(i) ==
    /\ i ∈ 1..N
    /\ state[i] = "Idle"
    /\ flags' = [flags EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<reg1, reg2, state>>

WriteTour1(i) ==
    /\ i ∈ 1..N
    /\ state[i] = "SetFlag"
    /\ reg1' = i
    /\ state' = [state EXCEPT ![i] = "ReadTour2"]
    /\ UNCHANGED <<flags, reg2>>

ReadTour2(i) ==
    /\ i ∈ 1..N
    /\ state[i] = "ReadTour2"
    /\ IF reg2 = i THEN
          state' = [state EXCEPT ![i] = "WaitOthers"]
       ELSE
          state' = [state EXCEPT ![i] = "SetFlag"]
    /\ UNCHANGED <<flags, reg1, reg2>>

WaitOthers(i) ==
    /\ i ∈ 1..N
    /\ state[i] = "WaitOthers"
    /\ (\A j \in 1..N : (j # i) => flags[j] = FALSE)
    /\ state' = [state EXCEPT ![i] = "CS"]
    /\ UNCHANGED <<flags, reg1, reg2>>

EnterCS(i) ==
    /\ i ∈ 1..N
    /\ state[i] = "CS"
    /\ reg2' = i
    /\ state' = [state EXCEPT ![i] = "Exit"]
    /\ UNCHANGED <<flags, reg1>>

Exit(i) ==
    /\ i ∈ 1..N
    /\ state[i] = "Exit"
    /\ flags' = [flags EXCEPT ![i] = FALSE]
    /\ reg1' = 0
    /\ reg2' = 0
    /\ state' = [state EXCEPT ![i] = "Idle"]

Next_i(i) ==
    SetIntent(i) \/ WriteTour1(i) \/ ReadTour2(i) \/ WaitOthers(i) \/ EnterCS(i) \/ Exit(i)

Next == \E i \in 1..N : Next_i(i)

vars == <<flags, reg1, reg2, state>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

MutualExclusion ==
    ∀ i,j ∈ 1..N :
        (i # j) => ~(state[i] = "CS" /\ state[j] = "CS")

StarvationFreedom ==
    ∀ i ∈ 1..N : □◇(state[i] = "Idle" => ◇(state[i] = "CS"))

THEOREM MutualExclusionHolds == Spec => []MutualExclusion
THEOREM StarvationFreedomHolds == Spec => StarvationFreedom

=============================================================================