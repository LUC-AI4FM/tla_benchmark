------------------------------ MODULE FischerTimed ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  N, \* number of processes
  Delta, \* per-process waiting time before checking x
  Epsilon, \* minimal time between two consecutive writes to x
  Infinity \* large sentinel value for timers

(*
Fischer's timed mutual exclusion algorithm, modeled in PlusCal with a separate
ticking process that decrements per-process timers and the global cooldown.

A bug should be found when N > 1 and Delta >= Epsilon, highlighting the
timing-sensitive design (typically a liveness violation).

PlusCal algorithm (for documentation):

--algorithm Fischer
variables x = 0, t = [i \in 1..N |-> Infinity], cool = 0;

fair process Tick = "tick"
  variable jj \in 1..N;
begin
tick:
  if (cool # Infinity /\ cool > 0)
     \/ (\E j \in 1..N: t[j] # Infinity /\ t[j] > 0) then
    for jj = 1 to N do
      if t[jj] # Infinity /\ t[jj] > 0 then
        t[jj] := t[jj] - 1
      end if;
    end for;
    if cool # Infinity /\ cool > 0 then
      cool := cool - 1
    end if;
  end if;
  goto tick;
end process;

process (i \in 1..N)
begin
Loop:
  skip; \* non-critical section
AwaitClear:
  await x = 0 /\ cool = 0;
SetX:
  x := self;
  cool := Epsilon;
SetTimer:
  t[self] := Delta;
WaitDelta:
  await t[self] = 0;
ClearTimer:
  t[self] := Infinity;
CheckX:
  if x = self then
cs:
    either goto exit
    or     goto cs
    end either;
exit:
    x := 0;
  end if;
  goto Loop;
end process;

end algorithm
*)

ASSUME
  /\ N \in Nat \ {0}
  /\ Delta \in Nat
  /\ Epsilon \in Nat
  /\ Infinity \in Nat
  /\ Infinity > Delta
  /\ Infinity > Epsilon

Proc == 1..N
ProcIds == Proc \cup {"tick"}

TimerVal == Nat \cup {Infinity}

LabelSet ==
  {"Loop","AwaitClear","SetX","SetTimer","WaitDelta","ClearTimer","CheckX","cs","exit","tick"}

VARIABLES x, t, cool, pc

vars == << x, t, cool, pc >>

Init ==
  /\ x = 0
  /\ t = [i \in Proc |-> Infinity]
  /\ cool = 0
  /\ pc = [i \in ProcIds |-> IF i \in Proc THEN "Loop" ELSE "tick"]

TickEnabled ==
  (cool # Infinity /\ cool > 0)
  \/ (\E j \in Proc: t[j] # Infinity /\ t[j] > 0)

TickStep ==
  /\ pc["tick"] = "tick"
  /\ TickEnabled
  /\ x' = x
  /\ t' = [j \in Proc |-> IF t[j] # Infinity /\ t[j] > 0 THEN t[j] - 1 ELSE t[j]]
  /\ cool' = IF cool # Infinity /\ cool > 0 THEN cool - 1 ELSE cool
  /\ pc' = pc

Loop(i) ==
  /\ i \in Proc
  /\ pc[i] = "Loop"
  /\ x' = x
  /\ t' = t
  /\ cool' = cool
  /\ pc' = [pc EXCEPT ![i] = "AwaitClear"]

AwaitClearAct(i) ==
  /\ i \in Proc
  /\ pc[i] = "AwaitClear"
  /\ x = 0 /\ cool = 0
  /\ x' = x
  /\ t' = t
  /\ cool' = cool
  /\ pc' = [pc EXCEPT ![i] = "SetX"]

SetXAct(i) ==
  /\ i \in Proc
  /\ pc[i] = "SetX"
  /\ x' = i
  /\ cool' = Epsilon
  /\ t' = t
  /\ pc' = [pc EXCEPT ![i] = "SetTimer"]

SetTimerAct(i) ==
  /\ i \in Proc
  /\ pc[i] = "SetTimer"
  /\ t' = [t EXCEPT ![i] = Delta]
  /\ x' = x
  /\ cool' = cool
  /\ pc' = [pc EXCEPT ![i] = "WaitDelta"]

WaitDeltaAct(i) ==
  /\ i \in Proc
  /\ pc[i] = "WaitDelta"
  /\ t[i] = 0
  /\ x' = x
  /\ t' = t
  /\ cool' = cool
  /\ pc' = [pc EXCEPT ![i] = "ClearTimer"]

ClearTimerAct(i) ==
  /\ i \in Proc
  /\ pc[i] = "ClearTimer"
  /\ t' = [t EXCEPT ![i] = Infinity]
  /\ x' = x
  /\ cool' = cool
  /\ pc' = [pc EXCEPT ![i] = "CheckX"]

CheckXAct(i) ==
  /\ i \in Proc
  /\ pc[i] = "CheckX"
  /\ x' = x
  /\ t' = t
  /\ cool' = cool
  /\ pc' = [pc EXCEPT ![i] = IF x = i THEN "cs" ELSE "Loop"]

CSStay(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ x' = x
  /\ t' = t
  /\ cool' = cool
  /\ pc' = [pc EXCEPT ![i] = "cs"]

CSGoExit(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ x' = x
  /\ t' = t
  /\ cool' = cool
  /\ pc' = [pc EXCEPT ![i] = "exit"]

ExitAct(i) ==
  /\ i \in Proc
  /\ pc[i] = "exit"
  /\ x' = 0
  /\ t' = t
  /\ cool' = cool
  /\ pc' = [pc EXCEPT ![i] = "Loop"]

Next ==
  TickStep
  \/ (\E i \in Proc:
        Loop(i) \/
        AwaitClearAct(i) \/
        SetXAct(i) \/
        SetTimerAct(i) \/
        WaitDeltaAct(i) \/
        ClearTimerAct(i) \/
        CheckXAct(i) \/
        CSStay(i) \/
        CSGoExit(i) \/
        ExitAct(i)
     )

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(TickStep)

TypeInv ==
  /\ x \in Proc \cup {0}
  /\ t \in [Proc -> TimerVal]
  /\ cool \in TimerVal
  /\ pc \in [ProcIds -> LabelSet]

Mutex ==
  Cardinality({ i \in Proc: pc[i] = "cs" }) <= 1

SomeProcessInfinitelyOftenInCS ==
  []<>(\E i \in Proc: pc[i] = "cs")

LabelCount(l) == Cardinality({ i \in Proc: pc[i] = l })

StateCounts ==
  [ loop |-> LabelCount("Loop"),
    wait |-> LabelCount("WaitDelta"),
    cs   |-> LabelCount("cs") ]

=============================================================================