------------------------------ MODULE RegularRing ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

(*
N-process shared-memory algorithm with regular registers.
Each process i writes its own register x[i] from {0} to {0,1} to {1},
then reads its neighbor's register x[Nbr(i)], where a read may return
any element currently in the set x[Nbr(i)].
*)

CONSTANT Val
ASSUME Val = {0, 1}

Allowed == { {0}, {0,1}, {1} }

Proc == 1..N

Nbr(i) == IF i < N THEN i + 1 ELSE 1

VARIABLES pc, x, y

vars == << pc, x, y >>

Init ==
  /\ pc = [i \in Proc |-> "wA"]
  /\ x  = [i \in Proc |-> {0}]
  /\ y  = [i \in Proc |-> 0]

WriteA(i) ==
  /\ i \in Proc
  /\ pc[i] = "wA"
  /\ x[i] = {0}
  /\ pc' = [pc EXCEPT ![i] = "wB"]
  /\ x'  = [x  EXCEPT ![i] = {0,1}]
  /\ UNCHANGED y

WriteB(i) ==
  /\ i \in Proc
  /\ pc[i] = "wB"
  /\ x[i] = {0,1}
  /\ pc' = [pc EXCEPT ![i] = "r"]
  /\ x'  = [x  EXCEPT ![i] = {1}]
  /\ UNCHANGED y

Read(i) ==
  /\ i \in Proc
  /\ pc[i] = "r"
  /\ LET j == Nbr(i) IN
       \E v \in x[j] :
         /\ y' = [y EXCEPT ![i] = v]
         /\ x' = x
  /\ pc' = [pc EXCEPT ![i] = "done"]

ProcStep(i) == WriteA(i) \/ WriteB(i) \/ Read(i)

Next == \E i \in Proc : ProcStep(i)

AllDone == \A i \in Proc : pc[i] = "done"

TypeOK ==
  /\ pc \in [Proc -> {"wA","wB","r","done"}]
  /\ x  \in [Proc -> Allowed]
  /\ y  \in [Proc -> Val]

RegPhases ==
  \A i \in Proc :
    /\ (pc[i] = "wA" => x[i] = {0})
    /\ (pc[i] = "wB" => x[i] \in {{0,1}, {1}})
    /\ (pc[i] \in {"r","done"} => x[i] = {1})

Inv == TypeOK /\ RegPhases

PCorrect == AllDone => (\E i \in Proc : y[i] = 1)

Fairness == \A i \in Proc : WF_vars(ProcStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

Termination == <>AllDone

THEOREM InvIsInvariant ==
  Spec => []Inv
PROOF OMITTED

THEOREM PCorrectness ==
  Spec => []PCorrect
PROOF OMITTED

===============================================================================