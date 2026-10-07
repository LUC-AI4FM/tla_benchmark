----------------------------- MODULE FischerTimed -----------------------------

EXTENDS Naturals, FiniteSets

(*
Fischer's timed mutual exclusion algorithm for N synchronizing processes,
with a separate ticking process that decrements per-process timers.

Timing is modeled using constants Delta and Epsilon and a large sentinel
value Infinity. The algorithm requires Epsilon < Delta for mutual exclusion.
A bug should be found when N > 1 and Delta >= Epsilon, highlighting the
timing-sensitive design.

PlusCal model (informal; see TLA+ translation below):

--algorithm Fischer
variables
  x = 0; \* shared register, 0 means free, i in Proc means owned by i
  tE = [i \in Proc |-> Infinity]; \* per-process epsilon-wait timers
  tD = [i \in Proc |-> 0];        \* per-process Delta cooldown timers

fair process (P \in Proc)
variable self = P;
begin
Ncrit:
  while TRUE do
  Try:
    await x = 0 /\ (\A k \in Proc: tD[k] = 0);
  SetX:
    x := self;
    tE[self] := Epsilon;
    tD[self] := Delta;
  WaitEps:
    await tE[self] = 0;
  Check:
    if x = self then
      CS:
        skip; \* critical section
      Exit:
        x := 0;
    end if;
  end while;
end process;

fair process (Tick = "tick")
begin
TickLoop:
  while TRUE do
  Tick:
    tE := [i \in Proc |-> IF tE[i] \in Nat /\ tE[i] > 0 THEN tE[i] - 1 ELSE tE[i]];
    tD := [i \in Proc |-> IF tD[i] \in Nat /\ tD[i] > 0 THEN tD[i] - 1 ELSE tD[i]];
  end while;
end process;

Notes:
- The ticking process decrements all positive, finite timers each step and leaves
  Infinity (the sentinel "disabled" value) and zero unchanged.
- Mutual exclusion holds if Epsilon < Delta.
- TLC can check the invariant MutualExclusion and the liveness property SomeInfCS.
- Named state counts (per-label counts) are provided for TLC inspection.
*)

CONSTANTS
  N,         \* number of processes
  Delta,     \* minimal separation between writes to x
  Epsilon,   \* minimal wait before checking x after writing
  Infinity   \* large sentinel for "disabled" timers

ASSUME
  /\ N \in Nat \ {0}
  /\ Delta \in Nat
  /\ Epsilon \in Nat
  /\ Infinity \in Nat
  /\ Infinity > Delta
  /\ Infinity > Epsilon

Proc == 1..N

TimerVal == Nat \cup {Infinity}

VARIABLES
  x,    \* shared register: 0 or a process id in Proc
  tE,   \* epsilon-wait timers: [Proc -> TimerVal]
  tD,   \* Delta cooldown timers: [Proc -> TimerVal]
  pc    \* control locations: [Proc \cup {"tick"} -> LabelSet]

LabelSetProc == {"Ncrit","SetX","WaitEps","Check","CS","Exit"}
LabelSet == LabelSetProc \cup {"Tick"}

vars == << x, tE, tD, pc >>

AllDeltaZero == \A k \in Proc : tD[k] = 0

DecTimer(t) ==
  [i \in Proc |-> IF t[i] \in Nat /\ t[i] > 0 THEN t[i] - 1 ELSE t[i]]

Init ==
  /\ x = 0
  /\ tE = [i \in Proc |-> Infinity]
  /\ tD = [i \in Proc |-> 0]
  /\ pc = [i \in (Proc \cup {"tick"}) |->
            IF i \in Proc THEN "Ncrit" ELSE "Tick"]

NcritToSet(i) ==
  /\ i \in Proc
  /\ pc[i] = "Ncrit"
  /\ x = 0
  /\ AllDeltaZero
  /\ pc' = [pc EXCEPT ![i] = "SetX"]
  /\ UNCHANGED << x, tE, tD >>

SetX(i) ==
  /\ i \in Proc
  /\ pc[i] = "SetX"
  /\ x' = i
  /\ tE' = [tE EXCEPT ![i] = Epsilon]
  /\ tD' = [tD EXCEPT ![i] = Delta]
  /\ pc' = [pc EXCEPT ![i] = "WaitEps"]

WaitEps(i) ==
  /\ i \in Proc
  /\ pc[i] = "WaitEps"
  /\ tE[i] = 0
  /\ pc' = [pc EXCEPT ![i] = "Check"]
  /\ UNCHANGED << x, tE, tD >>

CheckToCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "Check"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << x, tE, tD >>

CheckToNcrit(i) ==
  /\ i \in Proc
  /\ pc[i] = "Check"
  /\ x # i
  /\ pc' = [pc EXCEPT ![i] = "Ncrit"]
  /\ UNCHANGED << x, tE, tD >>

CSLeave(i) ==
  /\ i \in Proc
  /\ pc[i] = "CS"
  /\ pc' = [pc EXCEPT ![i] = "Exit"]
  /\ UNCHANGED << x, tE, tD >>

ExitToNcrit(i) ==
  /\ i \in Proc
  /\ pc[i] = "Exit"
  /\ x' = 0
  /\ pc' = [pc EXCEPT ![i] = "Ncrit"]
  /\ UNCHANGED << tE, tD >>

PNext(i) ==
  NcritToSet(i)
  \/ SetX(i)
  \/ WaitEps(i)
  \/ CheckToCS(i)
  \/ CheckToNcrit(i)
  \/ CSLeave(i)
  \/ ExitToNcrit(i)

Tick ==
  /\ pc["tick"] = "Tick"
  /\ tE' = DecTimer(tE)
  /\ tD' = DecTimer(tD)
  /\ pc' = pc
  /\ UNCHANGED x

Next ==
  \/ (\E i \in Proc : PNext(i))
  \/ Tick

TypeOK ==
  /\ x \in ({0} \cup Proc)
  /\ tE \in [Proc -> TimerVal]
  /\ tD \in [Proc -> TimerVal]
  /\ pc \in [Proc \cup {"tick"} -> LabelSet]

CSCount == Cardinality({ i \in Proc : pc[i] = "CS" })
NcritCount == Cardinality({ i \in Proc : pc[i] = "Ncrit" })
SetXCount == Cardinality({ i \in Proc : pc[i] = "SetX" })
WaitEpsCount == Cardinality({ i \in Proc : pc[i] = "WaitEps" })
CheckCount == Cardinality({ i \in Proc : pc[i] = "Check" })
ExitCount == Cardinality({ i \in Proc : pc[i] = "Exit" })

StateCount(l) == Cardinality({ i \in Proc : pc[i] = l })

CountsSumOK ==
  NcritCount + SetXCount + WaitEpsCount + CheckCount + CSCount + ExitCount = N

MutualExclusion == CSCount <= 1

SomeInfCS == []<>(\E i \in Proc : pc[i] = "CS")

Fairness ==
  /\ \A i \in Proc : WF_vars(PNext(i))
  /\ WF_vars(Tick)

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================