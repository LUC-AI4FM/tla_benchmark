----------------------------- MODULE Bakery -----------------------------
EXTENDS Naturals

CONSTANTS N, MaxTicket

ASSUME N \in Nat /\ N >= 1 /\ MaxTicket \in Nat /\ MaxTicket >= 0

ProcSet == 1..N
NumberSet == 0..MaxTicket
AuxDom == ProcSet \cup {0}

Max(S) == CHOOSE m \in S: \A n \in S: n <= m

(*
  Max number currently held by any process
*)
MaxNum(n) == Max({ n[j] : j \in ProcSet })

(*
  Fresh ticket value bounded by MaxTicket (for TLC finiteness).
  If the current maximum is at the bound, we saturate at MaxTicket.
*)
FreshNumber(n) == IF MaxNum(n) < MaxTicket THEN MaxNum(n) + 1 ELSE MaxTicket

VARIABLES pc, choosing, number, last

vars == << pc, choosing, number, last >>

Init ==
  /\ pc = [i \in ProcSet |-> "idle"]
  /\ choosing = [i \in ProcSet |-> FALSE]
  /\ number = [i \in ProcSet |-> 0]
  /\ last = 0

IdleToChoose(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "choose"]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED << number, last >>

ChooseToWait(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "choose"
  /\ LET new == FreshNumber(number) IN
       /\ number' = [number EXCEPT ![i] = new]
       /\ choosing' = [choosing EXCEPT ![i] = FALSE]
       /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ UNCHANGED last

WaitToCrit(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "wait"
  /\ \A j \in ProcSet:
       (j = i) \/
       (~choosing[j] /\
         (number[j] = 0 \/
          number[i] < number[j] \/
          (number[i] = number[j] /\ i < j)))
  /\ pc' = [pc EXCEPT ![i] = "crit"]
  /\ last' = i
  /\ UNCHANGED << choosing, number >>

CritToIdle(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "crit"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ number' = [number EXCEPT ![i] = 0]
  /\ UNCHANGED << choosing, last >>

ProcStep(i) == IdleToChoose(i) \/ ChooseToWait(i) \/ WaitToCrit(i) \/ CritToIdle(i)

Next == \E i \in ProcSet: ProcStep(i)

Fairness == \A i \in ProcSet: WF_vars(ProcStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(*
  Safety invariants
*)
TypeOK ==
  /\ pc \in [ProcSet -> {"idle", "choose", "wait", "crit"}]
  /\ choosing \in [ProcSet -> BOOLEAN]
  /\ number \in [ProcSet -> NumberSet]
  /\ last \in AuxDom

TicketBound ==
  \A i \in ProcSet: number[i] \in NumberSet

MutualExclusion ==
  \A i, j \in ProcSet: i # j => ~(pc[i] = "crit" /\ pc[j] = "crit")

=============================================================================