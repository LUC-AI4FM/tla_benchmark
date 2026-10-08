------------------------------ MODULE Fischer ------------------------------

EXTENDS Naturals, Integers, TLC

(*
  Fischer's real-time mutual exclusion algorithm for N processes with a discrete-time Tick.
  Processes 1..N loop through labels a–f and cs. Tick (process 0) decrements all timers
  simultaneously when all are strictly positive.
*)

CONSTANTS N, Delta, Epsilon

ASSUME /\ N \in Nat /\ N >= 1
       /\ Delta \in Nat /\ Epsilon \in Nat
       /\ Delta < Epsilon

Proc == 1..N

VARIABLES x, pc, t

Init ==
  /\ x = 0
  /\ pc = [i \in Proc |-> "a"]
  /\ t  = [i \in Proc |-> 0]

(*
  Process i control-flow actions (PlusCal-style labels a–f and cs):
    a: start of loop
    c: await x = 0
    d: set t[i] := Delta; x := i
    e: set t[i] := Epsilon; then wait until t[i] = 0
    b: if x = i then enter cs else restart
    cs: critical section
    f: exit cs; x := 0; restart
*)

A(i) == /\ i \in Proc
        /\ pc[i] = "a"
        /\ x' = x
        /\ t' = t
        /\ pc' = [pc EXCEPT ![i] = "c"]

C(i) == /\ i \in Proc
        /\ pc[i] = "c"
        /\ x = 0
        /\ x' = i
        /\ t' = [t EXCEPT ![i] = Delta]
        /\ pc' = [pc EXCEPT ![i] = "d"]

D(i) == /\ i \in Proc
        /\ pc[i] = "d"
        /\ x' = x
        /\ t' = [t EXCEPT ![i] = Epsilon]
        /\ pc' = [pc EXCEPT ![i] = "e"]

E(i) == /\ i \in Proc
        /\ pc[i] = "e"
        /\ t[i] = 0
        /\ x' = x
        /\ t' = t
        /\ pc' = [pc EXCEPT ![i] = "b"]

B(i) == /\ i \in Proc
        /\ pc[i] = "b"
        /\ x' = x
        /\ t' = t
        /\ pc' = [pc EXCEPT ![i] = IF x = i THEN "cs" ELSE "a"]

F(i) == /\ i \in Proc
        /\ pc[i] = "cs"
        /\ x' = 0
        /\ t' = t
        /\ pc' = [pc EXCEPT ![i] = "a"]

ProcAct(i) == A(i) \/ C(i) \/ D(i) \/ E(i) \/ B(i) \/ F(i)

(*
  Tick (process 0): decrement all timers at once iff every timer is strictly positive.
*)
Tick ==
  /\ \A i \in Proc: t[i] > 0
  /\ x' = x
  /\ pc' = pc
  /\ t' = [i \in Proc |-> t[i] - 1]

Next == Tick \/ (\E i \in Proc: ProcAct(i))

vars == << x, pc, t >>

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Tick)
        /\ \A i \in Proc: WF_vars(ProcAct(i))

InCS(i) == i \in Proc /\ pc[i] = "cs"
SomeInCS == \E i \in Proc: InCS(i)

Invariant == \A i, j \in Proc: (i /= j) => ~(InCS(i) /\ InCS(j))

Liveness == []<>(SomeInCS)

==============================