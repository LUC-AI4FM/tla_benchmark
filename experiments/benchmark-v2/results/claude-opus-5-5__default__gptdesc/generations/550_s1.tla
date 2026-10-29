---------------------------- MODULE Alternate ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Procs == 0 .. (N - 1)

(* --algorithm Alternate
variable turn = 0;

fair process (procs \in Procs)
begin
  ncs:   while TRUE do
           skip;
  enter:   await turn = self;
  cs:      skip;
  exit:    turn := (self + 1) % N;
         end while;
end process
end algorithm *)

\* BEGIN TRANSLATION
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

procs(self) == ncs(self) \/ enter(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs : procs(self))

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(procs(self))
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ turn \in Procs
          /\ pc \in [Procs -> {"ncs", "enter", "cs", "exit"}]

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] \in {"cs", "exit"} /\ pc[q] \in {"cs", "exit"})

TurnInv == \A p \in Procs : pc[p] \in {"cs", "exit"} => turn = p

(* Liveness properties *)

StarvationFree == \A p \in Procs : (pc[p] = "enter") ~> (pc[p] = "cs")

EventuallyCS == \A p \in Procs : []<>(pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion /\ TurnInv)
=============================================================================