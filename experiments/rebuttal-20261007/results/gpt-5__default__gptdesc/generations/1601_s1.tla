----------------------------- MODULE Fischer -----------------------------

EXTENDS Naturals, FiniteSets

(*
Fischer's timed mutual exclusion algorithm for N processes with a separate ticking
process that decrements per-process timers. Timing is modeled with constants
Delta and Epsilon plus a large sentinel value Infinity.

Note: A bug should be found when N > 1 and Delta >= Epsilon, reflecting the
timing-sensitive nature of the algorithm.

PlusCal sketch (for documentation); the TLA+ translation follows below.

--algorithm FischerAlgo
variables x = 0, y = [p \in Proc |-> Infinity];

fair process (P \in Proc)
variable self;
begin
  self := P;
ncs:
  y[self] := Delta;
try1:
  await y[self] = 0 /\ x = 0;
  x := self;
  y[self] := Epsilon;
try2:
  await y[self] = 0;
  if x = self then
cs:
    skip;
exit:
    x := 0;
    goto ncs;
  else
backoff:
    goto ncs;
  end if;
end process;

fair process (Tick = 0)
begin
tock:
  with p \in Proc do
    if y[p] \in Nat /\ y[p] > 0 then
      y[p] := y[p] - 1;
    end if;
  end with;
  goto tock;
end process;

end algorithm
*)

CONSTANTS
  N,         \* number of processes
  Delta,     \* delay before attempting to claim x
  Epsilon,   \* delay between claiming x and checking/entering CS
  Infinity   \* sentinel timer value (not in Nat)

ASSUME
  /\ N \in Nat /\ N >= 1
  /\ Delta \in Nat /\ Epsilon \in Nat

Proc == 1..N
PcVals == {"ncs", "try1", "try2", "cs"}

VARIABLES
  x,   \* shared register; 0 or a process id in Proc
  pc,  \* program counter mapping each process to a label in PcVals
  y    \* per-process timers in Nat or Infinity

vars == << x, pc, y >>

Init ==
  /\ x = 0
  /\ pc = [p \in Proc |-> "ncs"]
  /\ y  = [p \in Proc |-> Infinity]

NcsToTry(p) ==
  /\ p \in Proc
  /\ pc[p] = "ncs"
  /\ x' = x
  /\ pc' = [pc EXCEPT ![p] = "try1"]
  /\ y'  = [y EXCEPT ![p] = Delta]

Try1Claim(p) ==
  /\ p \in Proc
  /\ pc[p] = "try1"
  /\ y[p] \in Nat /\ y[p] = 0
  /\ x = 0
  /\ x' = p
  /\ pc' = [pc EXCEPT ![p] = "try2"]
  /\ y'  = [y EXCEPT ![p] = Epsilon]

Try2Enter(p) ==
  /\ p \in Proc
  /\ pc[p] = "try2"
  /\ y[p] \in Nat /\ y[p] = 0
  /\ x = p
  /\ x' = x
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED y

Try2Backoff(p) ==
  /\ p \in Proc
  /\ pc[p] = "try2"
  /\ y[p] \in Nat /\ y[p] = 0
  /\ x # p
  /\ x' = x
  /\ pc' = [pc EXCEPT ![p] = "ncs"]
  /\ y'  = [y EXCEPT ![p] = Infinity]

CsExit(p) ==
  /\ p \in Proc
  /\ pc[p] = "cs"
  /\ x' = 0
  /\ pc' = [pc EXCEPT ![p] = "ncs"]
  /\ y'  = [y EXCEPT ![p] = Infinity]

ProcStep(p) ==
  NcsToTry(p) \/ Try1Claim(p) \/ Try2Enter(p) \/ Try2Backoff(p) \/ CsExit(p)

Tick ==
  \E p \in Proc:
    /\ y[p] \in Nat /\ y[p] > 0
    /\ y' = [y EXCEPT ![p] = y[p] - 1]
    /\ x' = x
    /\ pc' = pc

Next ==
  Tick \/ (\E p \in Proc: ProcStep(p))

Spec ==
  Init /\ [][Next]_vars
  /\ WF_vars(Tick)
  /\ \A p \in Proc: WF_vars(ProcStep(p))

InCS(p) == p \in Proc /\ pc[p] = "cs"

MutualExclusion ==
  Cardinality({p \in Proc : pc[p] = "cs"}) <= 1

LiveSome ==
  \E p \in Proc: []<>(pc[p] = "cs")

StateCounts ==
  [ Ncs  |-> Cardinality({p \in Proc : pc[p] = "ncs"}),
    Try1 |-> Cardinality({p \in Proc : pc[p] = "try1"}),
    Try2 |-> Cardinality({p \in Proc : pc[p] = "try2"}),
    Cs   |-> Cardinality({p \in Proc : pc[p] = "cs"})
  ]

=============================================================================