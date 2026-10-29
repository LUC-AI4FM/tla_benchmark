---------------------------- MODULE Alternate ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 0..(N-1)

(* --algorithm Alternate
variables turn = 0;
process (procs \in Procs)
begin
  ncs:   while TRUE do
  enter:   await turn = self;
  crit:    skip;
  exit:    turn := (self + 1) % N;
         end while;
end process;
end algorithm; *)

VARIABLES turn, pc

vars == << turn, pc >>

ProcSet == Procs

Init == /\ turn = 0
        /\ pc = [self \in ProcSet |-> "ncs"]

NcsStep(self) == /\ pc[self] = "ncs"
                 /\ pc' = [pc EXCEPT ![self] = "enter"]
                 /\ UNCHANGED turn

EnterStep(self) == /\ pc[self] = "enter"
                   /\ turn = self
                   /\ pc' = [pc EXCEPT ![self] = "cs"]
                   /\ UNCHANGED turn

CsStep(self) == /\ pc[self] = "cs"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "exit"]
                /\ UNCHANGED turn

ExitStep(self) == /\ pc[self] = "exit"
                  /\ turn' = (self + 1) % N
                  /\ pc' = [pc EXCEPT ![self] = "ncs"]

procs(self) == NcsStep(self) \/ EnterStep(self) \/ CsStep(self) \/ ExitStep(self)

Next == (\E self \in Procs : procs(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(procs(self))

TypeOK == /\ turn \in Procs
          /\ pc \in [Procs -> {"ncs", "enter", "cs", "exit"}]

(* Mutual exclusion: at most one process is in its critical section *)
cs == \A i, j \in Procs : (pc[i] = "cs" /\ pc[j] = "cs") => (i = j)

=============================================================================