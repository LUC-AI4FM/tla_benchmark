--------------------------- MODULE RegularRing ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N
ASSUME N \in Nat \ {0}

VARIABLES pc, x, y, rdSeq

Proc == 1..N
Val == {0, 1}
NoVal == 2

Succ(i) == IF i = N THEN 1 ELSE i + 1

SeqToSet(s) == { s[k] : k \in DOMAIN s }
NoDupSeq(s) == \A i, j \in DOMAIN s : i # j => s[i] # s[j]

TypeOK ==
  /\ pc \in [Proc -> {"start", "write1", "read", "done"}]
  /\ x \in [Proc -> SUBSET Val]
  /\ y \in [Proc -> (Val \cup {NoVal})]
  /\ rdSeq \in Seq(Proc)

Init ==
  /\ pc = [i \in Proc |-> "start"]
  /\ x  = [i \in Proc |-> {0}]
  /\ y  = [i \in Proc |-> NoVal]
  /\ rdSeq = <<>>

WriteStart(i) ==
  /\ i \in Proc
  /\ pc[i] = "start"
  /\ pc' = [pc EXCEPT ![i] = "write1"]
  /\ x'  = [x  EXCEPT ![i] = {0, 1}]
  /\ UNCHANGED << y, rdSeq >>

WriteCommit(i) ==
  /\ i \in Proc
  /\ pc[i] = "write1"
  /\ pc' = [pc EXCEPT ![i] = "read"]
  /\ x'  = [x  EXCEPT ![i] = {1}]
  /\ UNCHANGED << y, rdSeq >>

Read(i) ==
  /\ i \in Proc
  /\ pc[i] = "read"
  /\ LET j == Succ(i) IN
       \E v \in x[j] :
         /\ y' = [y EXCEPT ![i] = v]
         /\ pc' = [pc EXCEPT ![i] = "done"]
         /\ rdSeq' = Append(rdSeq, i)
         /\ x' = x

Next ==
  \E i \in Proc : WriteStart(i) \/ WriteCommit(i) \/ Read(i)

vars == << pc, x, y, rdSeq >>

Spec == Init /\ [][Next]_vars

Terminated == \A i \in Proc : pc[i] = "done"

PCorrect == Terminated => (\E i \in Proc : y[i] = 1)

Inv ==
  /\ TypeOK
  /\ \A i \in Proc : pc[i] = "start" => /\ x[i] = {0} /\ y[i] = NoVal
  /\ \A i \in Proc : pc[i] = "write1" => x[i] = {0, 1}
  /\ \A i \in Proc : pc[i] \in {"read", "done"} => x[i] = {1}
  /\ NoDupSeq(rdSeq)
  /\ SeqToSet(rdSeq) \subseteq Proc
  /\ \A i \in Proc : pc[i] = "done" => i \in SeqToSet(rdSeq)

THEOREM InvIsInvariant ==
  Init /\ [][Next]_vars => []Inv
PROOF OMITTED

THEOREM PCorrectTheorem ==
  Spec => []PCorrect
PROOF OMITTED

============================================================================