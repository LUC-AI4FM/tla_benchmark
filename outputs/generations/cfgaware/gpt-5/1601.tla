------------------------------ MODULE FischerTimed ------------------------------

EXTENDS Naturals, TLC

(*
Fischer's timed mutual exclusion with a separate ticking process that decrements
per-process timers and a global write-separation timer.

Note: A timing bug should be found by TLC when N > 1 and Delta >= Epsilon,
illustrating the sensitivity of the design (try small values, e.g., N=2).
*)

CONSTANTS
  N,          \* number of processes
  Epsilon,    \* per-process minimal wait before checking
  Delta,      \* minimal separation between any two writes to x
  Infinity    \* a large sentinel value used for timers

ASSUME
  /\ N \in Nat /\ N >= 1
  /\ Epsilon \in Nat /\ Delta \in Nat
  /\ Infinity \in Nat /\ Infinity > Epsilon /\ Infinity > Delta

Proc == 1..N

(*
--algorithm Fischer
variables
  x = 0,                    \* shared register; 0 means free, p in Proc means owned
  g = 0,                    \* global "gate" timer enforcing at least Delta between writes
  t = [p \in Proc |-> Infinity];  \* per-process countdown timer, Infinity when idle

fair process (p \in Proc)
variable _;
begin
Idle:
  await x = 0 /\ g = 0;
  x := p;
  g := Delta;
  t[p] := Epsilon;

WaitE:
  await t[p] = 0;
  if x = p then
CS:
    skip;
Exit:
    x := 0;
    t[p] := Infinity;
    goto Idle;
  else
    t[p] := Infinity;
    goto Idle;
  end if;
end process;

fair process Tick = 0
begin
TickLoop:
  either
    if g > 0 then
      g := g - 1;
    else
      skip;
    end if;
  or
    with q \in Proc do
      if t[q] # Infinity /\ t[q] > 0 then
        t[q] := t[q] - 1;
      else
        skip;
      end if;
    end with;
  end either;
  goto TickLoop;
end process;

end algorithm
*)

VARIABLES x, g, t, pc

vars == << x, g, t, pc >>

Init ==
  /\ x = 0
  /\ g = 0
  /\ t = [p \in Proc |-> Infinity]
  /\ pc = [i \in Proc \cup {0} |->
            IF i = 0 THEN "TickLoop" ELSE "Idle"]

P_Idle(p) ==
  /\ p \in Proc
  /\ pc[p] = "Idle"
  /\ x = 0 /\ g = 0
  /\ x' = p
  /\ g' = Delta
  /\ t' = [t EXCEPT ![p] = Epsilon]
  /\ pc' = [pc EXCEPT ![p] = "WaitE"]

P_WaitE_to_CS(p) ==
  /\ p \in Proc
  /\ pc[p] = "WaitE"
  /\ t[p] = 0
  /\ x = p
  /\ t' = [t EXCEPT ![p] = Infinity]
  /\ pc' = [pc EXCEPT ![p] = "CS"]
  /\ UNCHANGED << x, g >>

P_WaitE_to_Idle(p) ==
  /\ p \in Proc
  /\ pc[p] = "WaitE"
  /\ t[p] = 0
  /\ x # p
  /\ t' = [t EXCEPT ![p] = Infinity]
  /\ pc' = [pc EXCEPT ![p] = "Idle"]
  /\ UNCHANGED << x, g >>

P_CS(p) ==
  /\ p \in Proc
  /\ pc[p] = "CS"
  /\ pc' = [pc EXCEPT ![p] = "Exit"]
  /\ UNCHANGED << x, g, t >>

P_Exit(p) ==
  /\ p \in Proc
  /\ pc[p] = "Exit"
  /\ x' = 0
  /\ pc' = [pc EXCEPT ![p] = "Idle"]
  /\ UNCHANGED << g, t >>

TickDecG ==
  /\ pc[0] = "TickLoop"
  /\ g > 0
  /\ g' = g - 1
  /\ pc' = pc
  /\ UNCHANGED << x, t >>

TickDecT ==
  /\ pc[0] = "TickLoop"
  /\ \E q \in Proc: t[q] # Infinity /\ t[q] > 0
  /\ \E q \in Proc:
       /\ t[q] # Infinity /\ t[q] > 0
       /\ t' = [t EXCEPT ![q] = @ - 1]
  /\ pc' = pc
  /\ UNCHANGED << x, g >>

ProcNext(p) ==
  P_Idle(p) \/ P_WaitE_to_CS(p) \/ P_WaitE_to_Idle(p) \/ P_CS(p) \/ P_Exit(p)

TickNext == TickDecG \/ TickDecT

Next ==
  \/ (\E p \in Proc: ProcNext(p))
  \/ TickNext

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc: WF_vars(ProcNext(p))
  /\ WF_vars(TickNext)

\* Mutual exclusion invariant: at most one process is in CS.
Invariant ==
  \A p, q \in Proc: p # q => ~(pc[p] = "CS" /\ pc[q] = "CS")

\* Liveness: some process is infinitely often in the critical section.
Liveness ==
  []<>(\E p \in Proc: pc[p] = "CS")

\* Optional TLC-friendly state counts (for inspection in the model checker).
NumIn(lab) == Cardinality({p \in Proc: pc[p] = lab})
NumInCS == NumIn("CS")
NumInIdle == NumIn("Idle")
NumInWait == NumIn("WaitE")
NumInExit == NumIn("Exit")

=============================================================================