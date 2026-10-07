```tla
MODULE NBAC

EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES nSntYes, nSntNo, nSntYesF, nSntNoF,
          nRcvdYes, nRcvdNo,
          pc, someFail

Init == (* Initial conditions *)
        /\ nSntYes = 0
        /\ nSntNo = 0
        /\ nSntYesF = 0
        /\ nSntNoF = 0
        /\ nRcvdYes = [i \in 1..N |-> 0]
        /\ nRcvdNo = [i \in 1..N |-> 0]
        /\ pc = [i \in 1..N |-> "YES"]
        /\ someFail = [i \in 1..N |-> FALSE]

SendYes(i) == (* Send YES vote *)
             /\ pc[i] = "YES"
             /\ nSntYes' = nSntYes + 1
             /\ pc' = [pc EXCEPT ![i] = "SENT"]
             /\ UNCHANGED <<nSntNo, nSntYesF, nSntNoF,
                             nRcvdYes, nRcvdNo, someFail>>

SendNo(i) == (* Send NO vote *)
            /\ pc[i] = "NO"
            /\ nSntNo' = nSntNo + 1
            /\ pc' = [pc EXCEPT ![i] = "SENT"]
            /\ UNCHANGED <<nSntYes, nSntYesF, nSntNoF,
                            nRcvdYes, nRcvdNo, someFail>>

Receive(i) == (* Receive votes *)
              /\ pc[i] = "SENT"
              /\ (nRcvdYes' = [nRcvdYes EXCEPT ![i] = nRcvdYes[i] + 1]
                   \/ nRcvdNo' = [nRcvdNo EXCEPT ![i] = nRcvdNo[i] + 1])
              /\ UNCHANGED <<nSntYes, nSntNo, nSntYesF, nSntNoF,
                              pc, someFail>>

Commit(i) == (* Commit *)
            /\ pc[i] = "SENT"
            /\ nRcvdYes[i] = N
            /\ nRcvdNo[i] = 0
            /\ pc' = [pc EXCEPT ![i] = "COMMIT"]
            /\ UNCHANGED <<nSntYes, nSntNo, nSntYesF, nSntNoF,
                            nRcvdYes, nRcvdNo, someFail>>

AbortSent(i) == (* Abort after sending *)
                /\ pc[i] = "SENT"
                /\ nRcvdNo[i] > 0
                /\ pc' = [pc EXCEPT ![i] = "ABORT"]
                /\ UNCHANGED <<nSntYes, nSntNo, nSntYesF, nSntNoF,
                                nRcvdYes, nRcvdNo, someFail>>

AbortNoYes(i) == (* Abort before sending *)
                 /\ pc[i] \in {"YES", "NO"}
                 /\ someFail[i]
                 /\ pc' = [pc EXCEPT ![i] = "ABORT"]
                 /\ UNCHANGED <<nSntYes, nSntNo, nSntYesF, nSntNoF,
                                 nRcvdYes, nRcvdNo, someFail>>

Crash(i) == (* Crash *)
           /\ pc[i] \in {"YES", "NO", "SENT"}
           /\ pc' = [pc EXCEPT ![i] = "BYZ"]
           /\ someFail' = [someFail EXCEPT ![i] = TRUE]
           /\ nSntYesF' = nSntYesF + 1
           /\ UNCHANGED <<nSntYes, nSntNo, nSntNoF,
                           nRcvdYes, nRcvdNo>>

Next == (* Next state *)
        \/ \E i \in 1..N : SendYes(i)
        \/ \E i \in 1..N : SendNo(i)
        \/ \E i \in 1..N : Receive(i)
        \/ \E i \in 1..N : Commit(i)
        \/ \E i \in 1..N : AbortSent(i)
        \/ \E i \in 1..N : AbortNoYes(i)
        \/ \E i \in 1..N : Crash(i)

Spec == (* Specification *)
       Init /\ [][Next]_<<nSntYes, nSntNo, nSntYesF, nSntNoF,
                       nRcvdYes, nRcvdNo, pc, someFail>>
       /\ WF_vars(<<SendYes, SendNo, Receive, Commit, AbortSent, AbortNoYes>>)

SpecYes == (* Specification with initial YES votes *)
          Init /\ [][Next]_<<nSntYes, nSntNo, nSntYesF, nSntNoF,
                          nRcvdYes, nRcvdNo, pc, someFail>>
          /\ WF_vars(<<SendYes, SendNo, Receive, Commit, AbortSent, AbortNoYes>>)
          /\ \A i \in 1..N : pc[i] = "YES"

SpecNo == (* Specification with initial NO votes *)
         Init /\ [][Next]_<<nSntYes, nSntNo, nSntYesF, nSntNoF,
                         nRcvdYes, nRcvdNo, pc, someFail>>
         /\ WF_vars(<<SendYes, SendNo, Receive, Commit, AbortSent, AbortNoYes>>)
         /\ \A i \in 1..N : pc[i] = "NO"

TypeOK == (* Type invariant *)
          /\ nSntYes \in Nat
          /\ nSntNo \in Nat
          /\ nSntYesF \in Nat
          /\ nSntNoF \in Nat
          /\ nRcvdYes \in [1..N -> Nat]
          /\ nRcvdNo \in [1..N -> Nat]
          /\ pc \in [1..N -> {"YES", "NO", "SENT", "ABORT", "COMMIT", "BYZ"}]
          /\ someFail \in [1..N -> Bool]

THEOREM Spec => []TypeOK
THEOREM Spec => \A i, j \in 1..N : pc[i] = "COMMIT" => pc[j] /= "ABORT"
THEOREM Spec => \A i \in 1..N : pc[i] = "COMMIT" => nSntNo = 0
THEOREM Spec => \A i \in 1..N : pc[i] = "ABORT" => nSntYes < N
THEOREM Spec => <>(\E i \in 1..N : pc[i] \in {"COMMIT", "ABORT"})
```