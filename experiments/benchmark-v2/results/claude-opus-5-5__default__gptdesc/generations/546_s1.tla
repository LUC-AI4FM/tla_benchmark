---- MODULE Alternate ----
EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 0..(N-1)

(* --algorithm Alternate
variable turn = 0;
process (p \in Procs)
begin
  ncs: while TRUE do
         skip;
  enter:   await turn = self;
  cs:      skip;
  exit:    turn := (self + 1) % N;
       end while;
end process
end algorithm *)

VARIABLES turn, pc

vars == << turn, pc >>

ProcSet == Procs

Init == /\ turn = 0
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ turn' = turn

enter(self) == /\ pc[self] = "enter"
               /\ turn = self
               /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ turn' = turn

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ turn' = turn

exit(self) == /\ pc[self] = "exit"
              /\ turn' = (self + 1) % N
              /\ pc' = [pc EXCEPT ![self] = "ncs"]

p(self) == ncs(self) \/ enter(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: p(self))

Spec == Init /\ [][Next]_vars

TypeOK == /\ turn \in Procs
          /\ pc \in [Procs -> {"ncs", "enter", "cs", "exit"}]

MutualExclusion == \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

====