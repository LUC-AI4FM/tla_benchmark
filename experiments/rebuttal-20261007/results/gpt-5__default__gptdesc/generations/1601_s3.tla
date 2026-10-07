----------------------------- MODULE Fischer -----------------------------
EXTENDS Naturals

CONSTANTS N, Delta, Epsilon, Infinity

(*
Fischer's timed mutual exclusion algorithm for N processes with a separate ticking process.

Timing model:
- Delta: maximum time (in discrete ticks) between reading x = 0 and writing x := i.
- Epsilon: minimum wait time (in discrete ticks) after writing x := i before checking x = i.
- Infinity: a large sentinel value used to denote "no active timer" for a process.

This PlusCal-style algorithm (informal; see TLA+ translation below) uses a per-process timer array
that the separate Ticker process decrements. Each process i proceeds:
- ncs: wait until x = 0, then start a Delta-sized "write window" timer and go to win.
- win: before the Delta window expires, write x := i, set timer to Epsilon, and go to wait.
        If the Delta window expires, give up and return to ncs.
- wait: wait until the Epsilon timer expires, then if x = i enter cs, else return to ncs.
- cs: leave the critical section by setting x := 0 and return to ncs.

A bug should be found by model checking when N > 1 and Delta >= Epsilon, which violates
the timing constraints Fischer's algorithm relies on.

We also maintain simple TLC-checkable counts of how many writes to x and how many entries to cs occur.

Liveness: some process is infinitely often in the critical section: []<>(∃i. pc[i] = "cs").

PlusCal sketch:

--algorithm Fischer
variables x = 0,
          timer = [i \in 1..N |-> Infinity],
          visits = ["write" |-> 0, "cs" |-> 0];

process (Proc \in 1..N)
variables me = Proc;
begin
ncs:
  await x = 0;
  timer[me] := Delta;
  goto win;

win:
  either
    when timer[me] > 0;
      x := me;
      timer[me] := Epsilon;
      visits["write"] := visits["write"] + 1;
      goto wait;
  or
    when timer[me] = 0;
      timer[me] := Infinity;
      goto ncs;
  end either;

wait:
  await timer[me] = 0;
  if x = me then
    visits["cs"] := visits["cs"] + 1;
    goto cs;
  else
    timer[me] := Infinity;
    goto ncs;
  end if;

cs:
  x := 0;
  goto ncs;
end process;

process (Ticker \in {0})
begin
tick:
  while TRUE do
    with i \in 1..N do
      if timer[i] \in Nat /\ timer[i] > 0 then
        timer[i] := timer[i] - 1;
      end if;
    end with;
  end while;
end process;

end algorithm
*)

ASSUME N \in Nat /\ N >= 1
ASSUME Delta \in Nat /\ Delta >= 0
ASSUME Epsilon \in Nat /\ Epsilon >= 0
ASSUME Infinity \notin Nat

Procs == 1..N
Labels == {"ncs", "win", "wait", "cs"}
CountLabels == {"write", "cs"}
TimerVal == Nat \cup {Infinity}

VARIABLES pc, x, timer, visits

TypeInv ==
  /\ pc \in [Procs -> Labels]
  /\ x \in {0} \cup Procs
  /\ timer \in [Procs -> TimerVal]
  /\ visits \in [CountLabels -> Nat]

Init ==
  /\ x = 0
  /\ pc = [i \in Procs |-> "ncs"]
  /\ timer = [i \in Procs |-> Infinity]
  /\ visits = [lab \in CountLabels |-> 0]
  /\ TypeInv

CanDec(i) == /\ i \in Procs /\ timer[i] \in Nat /\ timer[i] > 0

Tick(i) ==
  /\ i \in Procs
  /\ CanDec(i)
  /\ timer' = [timer EXCEPT ![i] = timer[i] - 1]
  /\ UNCHANGED <<pc, x, visits>>

ProcStart(i) ==
  /\ i \in Procs
  /\ pc[i] = "ncs"
  /\ x = 0
  /\ pc' = [pc EXCEPT ![i] = "win"]
  /\ timer' = [timer EXCEPT ![i] = Delta]
  /\ UNCHANGED <<x, visits>>

ProcWrite(i) ==
  /\ i \in Procs
  /\ pc[i] = "win"
  /\ timer[i] \in Nat /\ timer[i] > 0
  /\ x' = i
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ timer' = [timer EXCEPT ![i] = Epsilon]
  /\ visits' = [visits EXCEPT !["write"] = @ + 1]

ProcWinExpire(i) ==
  /\ i \in Procs
  /\ pc[i] = "win"
  /\ timer[i] = 0
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ timer' = [timer EXCEPT ![i] = Infinity]
  /\ UNCHANGED <<x, visits>>

ProcWaitCS(i) ==
  /\ i \in Procs
  /\ pc[i] = "wait"
  /\ timer[i] = 0
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ timer' = [timer EXCEPT ![i] = Infinity]
  /\ visits' = [visits EXCEPT !["cs"] = @ + 1]
  /\ UNCHANGED x

ProcWaitRetry(i) ==
  /\ i \in Procs
  /\ pc[i] = "wait"
  /\ timer[i] = 0
  /\ x # i
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ timer' = [timer EXCEPT ![i] = Infinity]
  /\ UNCHANGED <<x, visits>>

ProcCSExit(i) ==
  /\ i \in Procs
  /\ pc[i] = "cs"
  /\ x' = 0
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED <<timer, visits>>

Proc(i) ==
  ProcStart(i)
  \/ ProcWrite(i)
  \/ ProcWinExpire(i)
  \/ ProcWaitCS(i)
  \/ ProcWaitRetry(i)
  \/ ProcCSExit(i)

Next ==
  \/ \E i \in Procs: Proc(i)
  \/ \E i \in Procs: Tick(i)

vars == <<pc, x, timer, visits>>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Procs: WF_vars(Proc(i))
  /\ \A i \in Procs: WF_vars(Tick(i))

MutualExclusion ==
  \A i, j \in Procs: i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")

CountsOK ==
  /\ visits \in [CountLabels -> Nat]

SomeProcessInfinitelyOftenInCS ==
  []<>(\E i \in Procs: pc[i] = "cs")
============================================================================