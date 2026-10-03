---- MODULE Ring ----
EXTENDS Integers, FiniteSets

CONSTANT N
ASSUME N \in Nat \ {0}

(*--algorithm Ring
variables x = [i \in 0..N-1 |-> 0],
          y = [i \in 0..N-1 |-> 0];
process (P \in 0..N-1)
begin
L1: x[self] := 1;
L2: y[self] := x[(self-1) % N];
end process;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == <<x, y, pc>>
Procs == 0..N-1
Left(i) == (i - 1) % N

Init == (* Global variables *)
        /\ x = [i \in Procs |-> 0]
        /\ y = [i \in Procs |-> 0]
        /\ pc = [self \in Procs |-> "L1"]

L1(self) == /\ pc[self] = "L1"
            /\ x' = [x EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "L2"]
            /\ UNCHANGED <<y>>

L2(self) == /\ pc[self] = "L2"
            /\ y' = [y EXCEPT ![self] = x[Left(self)]]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED <<x>>

P(self) == L1(self) \/ L2(self)

Next == EXISTS self \in Procs: P(self)

Spec == Init /\ [][Next]_vars

Termination == <>(FORALL self \in Procs: pc[self] = "Done")

\* END TRANSLATION

TypeOK == /\ x \in [Procs -> {0, 1}]
          /\ y \in [Procs -> {0, 1}]
          /\ pc \in [Procs -> {"L1", "L2", "Done"}]

Inv == /\ TypeOK
       /\ FORALL i \in Procs: x[i] = 1 <=> pc[i] # "L1"
       /\ FORALL i \in Procs:
            (pc[i] = "Done" /\ y[i] = 0) => (pc[Left(i)] = "L1")

AllDone == FORALL i \in Procs: pc[i] = "Done"
SomeYis1 == EXISTS i \in Procs: y[i] = 1

PCorrect == AllDone => SomeYis1

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
<1> Init => Inv
  OBVIOUS
<2> Inv /\ [Next]_vars => Inv'
  OMITTED
<3> QED
  BY <1>, <2>, PTL DEF Spec

THEOREM Inv => PCorrect
<1> ASSUME Inv, AllDone
    PROVE  SomeYis1
  <2> SUFFICES ASSUME FORALL i \in Procs: y[i] = 0
               PROVE  FALSE
    <3> FORALL i \in Procs: pc[Left(i)] = "L1"
      <4> CHOOSE i \in Procs
        <5> pc[i] = "Done"
          BY ASSUME AllDone
        <5> y[i] = 0
          BY ASSUME
        <5> (pc[i] = "Done" /\ y[i] = 0) => (pc[Left(i)] = "L1")
          BY ASSUME Inv
        <5> QED
          BY <5>1, <5>2, <5>3
      <4> QED
        BY <4>
    <3> FORALL j \in Procs: pc[j] = "L1"
      LET f[i \in Procs] == Left(i)
      HAVE f[Procs] = Procs
        BY OMITTED (* Standard property of modulo arithmetic *)
      THEN QED
        BY <3>1
    <3> CHOOSE i \in Procs
      BY ASSUME N > 0 DEF Procs
    <3> pc[i] = "Done"
      BY ASSUME AllDone
    <3> pc[i] = "L1"
      BY <3>2
    <3> QED
      BY <3>4, <3>5
  <2> QED
    BY <2>
<1> QED
  BY <1>

THEOREM Spec => []PCorrect
  BY Inv => PCorrect, Spec => []Inv

=============================================================================