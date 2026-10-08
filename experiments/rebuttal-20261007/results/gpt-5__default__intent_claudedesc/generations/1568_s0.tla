------------------------------ MODULE Bakery ------------------------------

EXTENDS Integers, Naturals

CONSTANTS Proc, MaxNum

ASSUME Proc # {} /\ Proc \subseteq Nat /\ MaxNum \in Nat /\ MaxNum >= 1

VARIABLES choosing, number, pc

Ticket == 0..MaxNum

vars == << choosing, number, pc >>

TypeOK ==
  /\ choosing \in [Proc -> BOOLEAN]
  /\ number \in [Proc -> Ticket]
  /\ pc \in [Proc -> {"idle", "choose", "wait", "cs"}]

MaxOf(S) == IF S = {} THEN 0 ELSE CHOOSE m \in S : \A n \in S : n <= m

Prior(i, j) ==
  \/ number[i] < number[j]
  \/ (number[i] = number[j] /\ i < j)

CanEnter(i) ==
  \A j \in Proc :
    (j = i) \/ (~choosing[j] /\ (number[j] = 0 \/ Prior(i, j)))

Init ==
  /\ TypeOK
  /\ choosing = [i \in Proc |-> FALSE]
  /\ number   = [i \in Proc |-> 0]
  /\ pc       = [i \in Proc |-> "idle"]

StartChoose(i) ==
  /\ i \in Proc
  /\ pc[i] = "idle"
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ pc'       = [pc EXCEPT ![i] = "choose"]
  /\ UNCHANGED number

PickNumber(i) ==
  /\ i \in Proc
  /\ pc[i] = "choose"
  /\ LET S == { number[j] : j \in Proc } IN
     LET m == MaxOf(S) IN
     LET new == IF m < MaxNum THEN m + 1 ELSE MaxNum IN
       /\ number'  = [number EXCEPT ![i] = new]
       /\ choosing' = [choosing EXCEPT ![i] = FALSE]
       /\ pc'       = [pc EXCEPT ![i] = "wait"]

EnterCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait"
  /\ CanEnter(i)
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << choosing, number >>

ExitCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ number' = [number EXCEPT ![i] = 0]
  /\ pc'     = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED choosing

ProcNext(i) == StartChoose(i) \/ PickNumber(i) \/ EnterCS(i) \/ ExitCS(i)

Next == \E i \in Proc : ProcNext(i)

Spec == Init /\ [][Next]_vars /\ \A i \in Proc : WF_vars(ProcNext(i))

MutualExclusion ==
  \A p, q \in Proc : p # q => ~(pc[p] = "cs" /\ pc[q] = "cs")

=============================================================================