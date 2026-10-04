---------------------------- MODULE NBAC ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

VARIABLES
    pc,
    nSntYes,
    nSntNo,
    nSntYesF,
    nSntNoF,
    nRcvdYes,
    nRcvdNo,
    someFail

vars == <<pc, nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

Status == {"YES", "NO", "SENT", "ABORT", "COMMIT", "BYZ"}

TypeOK ==
    /\ pc \in [Procs -> Status]
    /\ nSntYes \in 0..N
    /\ nSntNo \in 0..N
    /\ nSntYesF \in 0..N
    /\ nSntNoF \in 0..N
    /\ nRcvdYes \in [Procs -> 0..N]
    /\ nRcvdNo \in [Procs -> 0..N]
    /\ someFail \in [Procs -> BOOLEAN]

InitYes ==
    /\ pc = [i \in Procs |-> "YES"]
    /\ nSntYes = 0
    /\ nSntNo = 0
    /\ nSntYesF = 0
    /\ nSntNoF = 0
    /\ nRcvdYes = [i \in Procs |-> 0]
    /\ nRcvdNo = [i \in Procs |-> 0]
    /\ someFail = [i \in Procs |-> FALSE]

InitNo ==
    /\ pc \in [Procs -> {"YES", "NO"}]
    /\ \E i \in Procs : pc[i] = "NO"
    /\ nSntYes = 0
    /\ nSntNo = 0
    /\ nSntYesF = 0
    /\ nSntNoF = 0
    /\ nRcvdYes = [i \in Procs |-> 0]
    /\ nRcvdNo = [i \in Procs |-> 0]
    /\ someFail = [i \in Procs |-> FALSE]

Init ==
    /\ pc \in [Procs -> {"YES", "NO"}]
    /\ nSntYes = 0
    /\ nSntNo = 0
    /\ nSntYesF = 0
    /\ nSntNoF = 0
    /\ nRcvdYes = [i \in Procs |-> 0]
    /\ nRcvdNo = [i \in Procs |-> 0]
    /\ someFail = [i \in Procs |-> FALSE]

Suspected(i) == someFail[i]

SendYes(i) ==
    /\ pc[i] = "YES"
    /\ ~Suspected(i)
    /\ pc' = [pc EXCEPT ![i] = "SENT"]
    /\ nSntYes' = nSntYes + 1
    /\ UNCHANGED <<nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

SendNo(i) ==
    /\ pc[i] = "NO"
    /\ ~Suspected(i)
    /\ pc' = [pc EXCEPT ![i] = "SENT"]
    /\ nSntNo' = nSntNo + 1
    /\ UNCHANGED <<nSntYes, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

Receive(i) ==
    /\ pc[i] = "SENT"
    /\ \/ /\ nRcvdYes[i] < nSntYes + nSntYesF
          /\ nRcvdYes' = [nRcvdYes EXCEPT ![i] = nRcvdYes[i] + 1]
          /\ UNCHANGED nRcvdNo
       \/ /\ nRcvdNo[i] < nSntNo + nSntNoF
          /\ nRcvdNo' = [nRcvdNo EXCEPT ![i] = nRcvdNo[i] + 1]
          /\ UNCHANGED nRcvdYes
    /\ UNCHANGED <<pc, nSntYes, nSntNo, nSntYesF, nSntNoF, someFail>>

Commit(i) ==
    /\ pc[i] = "SENT"
    /\ nRcvdYes[i] = N
    /\ nRcvdNo[i] = 0
    /\ pc' = [pc EXCEPT ![i] = "COMMIT"]
    /\ UNCHANGED <<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

AbortSent(i) ==
    /\ pc[i] = "SENT"
    /\ nRcvdNo[i] > 0
    /\ pc' = [pc EXCEPT ![i] = "ABORT"]
    /\ UNCHANGED <<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

AbortNoYes(i) ==
    /\ pc[i] \in {"YES", "NO"}
    /\ \E j \in Procs : Suspected(j)
    /\ pc' = [pc EXCEPT ![i] = "ABORT"]
    /\ UNCHANGED <<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

Crash(i) ==
    /\ pc[i] \in {"YES", "NO", "SENT"}
    /\ pc' = [pc EXCEPT ![i] = "BYZ"]
    /\ someFail' = [someFail EXCEPT ![i] = TRUE]
    /\ IF pc[i] = "YES"
       THEN /\ nSntYesF' = nSntYesF + 1
            /\ UNCHANGED nSntNoF
       ELSE IF pc[i] = "NO"
            THEN /\ nSntNoF' = nSntNoF + 1
                 /\ UNCHANGED nSntYesF
            ELSE UNCHANGED <<nSntYesF, nSntNoF>>
    /\ UNCHANGED <<nSntYes, nSntNo, nRcvdYes, nRcvdNo>>

NonCrashAction(i) ==
    \/ SendYes(i)
    \/ SendNo(i)
    \/ Receive(i)
    \/ Commit(i)
    \/ AbortSent(i)
    \/ AbortNoYes(i)

Next ==
    \E i \in Procs :
        \/ NonCrashAction(i)
        \/ Crash(i)

Fairness == \A i \in Procs : WF_vars(NonCrashAction(i))

Spec == Init /\ [][Next]_vars /\ Fairness

SpecYes == InitYes /\ [][Next]_vars /\ Fairness

SpecNo == InitNo /\ [][Next]_vars /\ Fairness

Decided(i) == pc[i] \in {"COMMIT", "ABORT"}

Agreement ==
    \A i, j \in Procs :
        ~(pc[i] = "COMMIT" /\ pc[j] = "ABORT")

AbortValidity ==
    (\E i \in Procs : pc[i] = "NO" \/ (pc[i] = "BYZ" /\ nSntNoF > 0)) =>
        \A j \in Procs : pc[j] # "COMMIT"

CommitValidity ==
    ((\A i \in Procs : pc[i] \in {"YES", "SENT", "COMMIT"} \/ (pc[i] = "BYZ" /\ nSntYesF > 0)) /\ 
     (\A i \in Procs : ~Suspected(i))) =>
        \A j \in Procs : pc[j] # "ABORT"

NoCrash == \A i \in Procs : pc[i] # "BYZ"

NoSuspicion == \A i \in Procs : ~someFail[i]

Termination ==
    [](NoCrash /\ NoSuspicion) => <>(\A i \in Procs : Decided(i))

=============================================================================