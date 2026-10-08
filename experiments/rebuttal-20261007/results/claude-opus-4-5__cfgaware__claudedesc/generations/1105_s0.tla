---------------------------- MODULE NBAC ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLES pc, nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail

vars == <<pc, nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

Procs == 1..N

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

Init ==
    /\ pc \in [Procs -> {"YES", "NO"}]
    /\ nSntYes = 0
    /\ nSntNo = 0
    /\ nSntYesF = 0
    /\ nSntNoF = 0
    /\ nRcvdYes = [p \in Procs |-> 0]
    /\ nRcvdNo = [p \in Procs |-> 0]
    /\ someFail = [p \in Procs |-> FALSE]

InitYes ==
    /\ pc = [p \in Procs |-> "YES"]
    /\ nSntYes = 0
    /\ nSntNo = 0
    /\ nSntYesF = 0
    /\ nSntNoF = 0
    /\ nRcvdYes = [p \in Procs |-> 0]
    /\ nRcvdNo = [p \in Procs |-> 0]
    /\ someFail = [p \in Procs |-> FALSE]

InitNo ==
    /\ \E q \in Procs : pc = [p \in Procs |-> IF p = q THEN "NO" ELSE "YES"]
    /\ nSntYes = 0
    /\ nSntNo = 0
    /\ nSntYesF = 0
    /\ nSntNoF = 0
    /\ nRcvdYes = [p \in Procs |-> 0]
    /\ nRcvdNo = [p \in Procs |-> 0]
    /\ someFail = [p \in Procs |-> FALSE]

Suspected(p) == someFail[p]

SendYes(p) ==
    /\ pc[p] = "YES"
    /\ ~Suspected(p)
    /\ pc' = [pc EXCEPT ![p] = "SENT"]
    /\ nSntYes' = nSntYes + 1
    /\ UNCHANGED <<nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

SendNo(p) ==
    /\ pc[p] = "NO"
    /\ ~Suspected(p)
    /\ pc' = [pc EXCEPT ![p] = "SENT"]
    /\ nSntNo' = nSntNo + 1
    /\ UNCHANGED <<nSntYes, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

Receive(p) ==
    /\ pc[p] = "SENT"
    /\ \/ /\ nRcvdYes[p] < nSntYes + nSntYesF
          /\ nRcvdYes' = [nRcvdYes EXCEPT ![p] = nRcvdYes[p] + 1]
          /\ UNCHANGED nRcvdNo
       \/ /\ nRcvdNo[p] < nSntNo + nSntNoF
          /\ nRcvdNo' = [nRcvdNo EXCEPT ![p] = nRcvdNo[p] + 1]
          /\ UNCHANGED nRcvdYes
    /\ UNCHANGED <<pc, nSntYes, nSntNo, nSntYesF, nSntNoF, someFail>>

Commit(p) ==
    /\ pc[p] = "SENT"
    /\ nRcvdYes[p] = N
    /\ nRcvdNo[p] = 0
    /\ pc' = [pc EXCEPT ![p] = "COMMIT"]
    /\ UNCHANGED <<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

AbortSent(p) ==
    /\ pc[p] = "SENT"
    /\ nRcvdNo[p] > 0
    /\ pc' = [pc EXCEPT ![p] = "ABORT"]
    /\ UNCHANGED <<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

AbortNoYes(p) ==
    /\ pc[p] \in {"YES", "NO"}
    /\ \E q \in Procs : Suspected(q)
    /\ pc' = [pc EXCEPT ![p] = "ABORT"]
    /\ UNCHANGED <<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

Crash(p) ==
    /\ pc[p] \in {"YES", "NO", "SENT"}
    /\ pc' = [pc EXCEPT ![p] = "BYZ"]
    /\ someFail' = [someFail EXCEPT ![p] = TRUE]
    /\ IF pc[p] = "YES"
       THEN /\ nSntYesF' = nSntYesF + 1
            /\ UNCHANGED nSntNoF
       ELSE IF pc[p] = "NO"
            THEN /\ nSntNoF' = nSntNoF + 1
                 /\ UNCHANGED nSntYesF
            ELSE UNCHANGED <<nSntYesF, nSntNoF>>
    /\ UNCHANGED <<nSntYes, nSntNo, nRcvdYes, nRcvdNo>>

NonCrashAction(p) ==
    \/ SendYes(p)
    \/ SendNo(p)
    \/ Receive(p)
    \/ Commit(p)
    \/ AbortSent(p)
    \/ AbortNoYes(p)

Next ==
    \E p \in Procs :
        \/ NonCrashAction(p)
        \/ Crash(p)

Fairness == \A p \in Procs : WF_vars(NonCrashAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

SpecYes == InitYes /\ [][Next]_vars /\ Fairness

SpecNo == InitNo /\ [][Next]_vars /\ Fairness

Decided(p) == pc[p] \in {"COMMIT", "ABORT"}

Agreement ==
    \A p, q \in Procs :
        (pc[p] = "COMMIT" /\ pc[q] = "ABORT") => FALSE

AgrrLtl == []Agreement

AbortValidity ==
    (\E p \in Procs : pc[p] = "NO" \/ (pc[p] = "BYZ" /\ nSntNoF > 0))
        => ~(\E q \in Procs : pc[q] = "COMMIT")

AbortValidityLtl == []AbortValidity

AllVotedYes == \A p \in Procs : pc[p] \in {"YES", "SENT", "COMMIT"}

NoSuspicions == \A p \in Procs : ~someFail[p]

CommitValidity ==
    (AllVotedYes /\ NoSuspicions) => ~(\E p \in Procs : pc[p] = "ABORT")

CommitValidityLtl == []CommitValidity

NoCrashes == \A p \in Procs : pc[p] # "BYZ"

AllDecided == \A p \in Procs : pc[p] \in {"COMMIT", "ABORT", "BYZ"}

TerminationLtl == [](NoCrashes /\ NoSuspicions) => <>AllDecided

=============================================================================