----------------------------- MODULE Ring -----------------------------
EXTENDS Integers, TLC, Sequences

CONSTANTS N
ASSUME N \in Nat /\ N > 0

(*--algorithm Ring
variables x = [i \in 1..N |-> 0],
          y = [i \in 1..N |-> 0] ;

process (proc \in 1..N)
{
  L1:
    x[self] := 1;
  L2:
    y[self] := x[if self = 1 then N else self-1];
}
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (1..N)

Left(i) == IF i=1 THEN N ELSE i-1

L1(self) == /\ pc[self] = "L1"
            /\ x' = [x EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "L2"]
            /\ y' = y

L2(self) == /\ pc[self] = "L2"
            /\ y' = [y EXCEPT ![self] = x[Left(self)]]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ x' = x

proc(self) == L1(self) \/ L2(self)

Next == \E self \in 1..N : proc(self)

Init == (* Global variables *)
        /\ x = [i \in 1..N |-> 0]
        /\ y = [i \in 1..N |-> 0]
        /\ pc = [self \in 1..N |-> "L1"]

Spec == Init /\ [][Next]_vars

Fairness == \A self \in 1..N : WF_vars(proc(self))

\* END TRANSLATION

=============================================================================