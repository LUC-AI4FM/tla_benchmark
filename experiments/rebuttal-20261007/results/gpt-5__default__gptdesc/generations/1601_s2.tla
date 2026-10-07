------------------------------ MODULE FischerMutex ------------------------------
EXTENDS Naturals, FiniteSets, TLC

(*
Fischer's timed mutual exclusion algorithm with N synchronizing processes and a
separate ticking process that decrements per-process timers.

Timing is modeled with constants Delta (deadline to perform the write after seeing
turn = None) and Epsilon (minimum wait before checking turn after writing), plus a
large sentinel value Infinity used to indicate "no active timer".

A known bug should be found by TLC when N > 1 and Delta >= Epsilon, reflecting the
timing-sensitive nature of the algorithm: mutual exclusion can be violated in that
case. When Delta < Epsilon, the mutual exclusion invariant should hold.

We also include:
- A safety invariant for mutual exclusion.
- A liveness property stating that some process is infinitely often in the critical section.
- A TLC-friendly check of named state counts per control point (labels).
*)

CONSTANTS
  N \in Nat \ {0},        \* number of processes, N >= 1
  Delta \in Nat,          \* write-deadline bound (must write within Delta after seeing turn=None)
  Epsilon \in Nat,        \* minimum delay before checking after writing turn := self
  Infinity \in Nat        \* large sentinel, assumed > Delta + Epsilon + 1 in the model

(*
PlusCal algorithm (for documentation); the TLA+ translation appears below.

--algorithm Fischer
variables
  turn = None,
  timer = [p \in Proc |-> Infinity];

fair process (p \in Proc)
begin
ncs:
  goto try;

try:
  await turn = None;
  timer[p] := Delta;
  goto setturn;

setturn:
  if timer[p] > 0 then
    turn := p;
    timer[p] := Epsilon;
    goto wait;
  else
    timer[p] := Infinity;
    goto try;
  end if;

wait:
  await timer[p] = 0;
  goto check;

check:
  if turn = p then
    goto crit;
  else
    goto try;
  end if;

crit:
  skip;
  goto exit;

exit:
  turn := None;
  timer[p] := Infinity;
  goto ncs;
end process;

fair process Ticker = "tick"
begin
tick:
  while TRUE do
    for i \in Proc do
      if timer[i] # Infinity /\ timer[i] > 0 then
        timer[i] := timer[i] - 1;
      end if;
    end for;
  end while;
end process;

end algorithm
*)

(***************************************************************************)
(*                    TLA+ translation of the algorithm                    *)
(***************************************************************************)

None == 0
Proc == 1..N
TickerId == "tickProc"           \* identifier for the ticking process in pc
TickLabel == "tick"              \* its single control location

ProcLabels == {"ncs","try","setturn","wait","check","crit","exit"}
AllLabels == ProcLabels \cup {TickLabel}

VARIABLES pc, turn, timer

vars == << pc, turn, timer >>

TypeInv ==
  /\ turn \in (Proc \cup {None})
  /\ timer \in [Proc -> 0..Infinity]
  /\ DOMAIN pc = Proc \cup {TickerId}
  /\ \A p \in Proc: pc[p] \in ProcLabels
  /\ pc[TickerId] = TickLabel

Init ==
  /\ pc = [x \in (Proc \cup {TickerId}) |-> IF x \in Proc THEN "ncs" ELSE TickLabel]
  /\ turn = None
  /\ timer = [p \in Proc |-> Infinity]

NCS(p) ==
  /\ p \in Proc
  /\ pc[p] = "ncs"
  /\ pc' = [pc EXCEPT ![p] = "try"]
  /\ UNCHANGED << turn, timer >>

Try(p) ==
  /\ p \in Proc
  /\ pc[p] = "try"
  /\ turn = None
  /\ timer' = [timer EXCEPT ![p] = Delta]
  /\ pc' = [pc EXCEPT ![p] = "setturn"]
  /\ UNCHANGED turn

SetTurn_Write(p) ==
  /\ p \in Proc
  /\ pc[p] = "setturn"
  /\ timer[p] > 0
  /\ turn' = p
  /\ timer' = [timer EXCEPT ![p] = Epsilon]
  /\ pc' = [pc EXCEPT ![p] = "wait"]

SetTurn_Timeout(p) ==
  /\ p \in Proc
  /\ pc[p] = "setturn"
  /\ ~(timer[p] > 0)
  /\ timer' = [timer EXCEPT ![p] = Infinity]
  /\ pc' = [pc EXCEPT ![p] = "try"]
  /\ UNCHANGED turn

WaitEps(p) ==
  /\ p \in Proc
  /\ pc[p] = "wait"
  /\ timer[p] = 0
  /\ pc' = [pc EXCEPT ![p] = "check"]
  /\ UNCHANGED << turn, timer >>

Check_OK(p) ==
  /\ p \in Proc
  /\ pc[p] = "check"
  /\ turn = p
  /\ pc' = [pc EXCEPT ![p] = "crit"]
  /\ UNCHANGED << turn, timer >>

Check_Retry(p) ==
  /\ p \in Proc
  /\ pc[p] = "check"
  /\ turn # p
  /\ pc' = [pc EXCEPT ![p] = "try"]
  /\ UNCHANGED << turn, timer >>

CritStep(p) ==
  /\ p \in Proc
  /\ pc[p] = "crit"
  /\ pc' = [pc EXCEPT ![p] = "exit"]
  /\ UNCHANGED << turn, timer >>

ExitStep(p) ==
  /\ p \in Proc
  /\ pc[p] = "exit"
  /\ turn' = None
  /\ timer' = [timer EXCEPT ![p] = Infinity]
  /\ pc' = [pc EXCEPT ![p] = "ncs"]

Tick ==
  /\ pc[TickerId] = TickLabel
  /\ timer' = [i \in Proc |-> IF (timer[i] # Infinity) /\ (timer[i] > 0) THEN timer[i] - 1 ELSE timer[i]]
  /\ pc' = pc
  /\ UNCHANGED turn

ProcStep(p) ==
  NCS(p)
  \/ Try(p)
  \/ SetTurn_Write(p)
  \/ SetTurn_Timeout(p)
  \/ WaitEps(p)
  \/ Check_OK(p)
  \/ Check_Retry(p)
  \/ CritStep(p)
  \/ ExitStep(p)

Next ==
  \/ (\E p \in Proc: ProcStep(p))
  \/ Tick

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Tick)   \* Fairness for the ticker: if it remains enabled, it eventually ticks.

(***************************************************************************)
(*                         Safety and liveness                             *)
(***************************************************************************)

Crit(p) == p \in Proc /\ pc[p] = "crit"

MutualExclusion ==
  \A p, q \in Proc: (p # q) => ~(Crit(p) /\ Crit(q))

Invariant == TypeInv /\ MutualExclusion

InfOftenCS == []<>(\E p \in Proc: Crit(p))

(***************************************************************************)
(*                   TLC-friendly state-count helpers                      *)
(***************************************************************************)

CountAt(l) == Cardinality({p \in Proc: pc[p] = l})

Counts == [ l \in ProcLabels |-> CountAt(l) ]

StateCountInv ==
  /\ \A p \in Proc: pc[p] \in ProcLabels
  /\ Counts["ncs"] + Counts["try"] + Counts["setturn"]
     + Counts["wait"] + Counts["check"] + Counts["crit"] + Counts["exit"] = N

=============================================================================