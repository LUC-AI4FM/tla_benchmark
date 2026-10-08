------------------------------- MODULE RingRingRW -------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 1

(*
  N processes arranged in a ring, indexed by Proc = 0..N-1.
  Each process i:
    - First writes 1 into its own shared register Reg[i].
    - Then reads the left neighbor's register Reg[Left(i)] into its local result Res[i].
  Control states per process: "Before" (before first step), "Between" (after write, before read), "Terminated" (after read).
*)

Proc == 0..(N - 1)

Left(i) == IF i = 0 THEN N - 1 ELSE i - 1

VARIABLES Reg, Res, pc

vars == << Reg, Res, pc >>

Init ==
  /\ Reg = [i \in Proc |-> 0]
  /\ Res = [i \in Proc |-> 0]
  /\ pc  = [i \in Proc |-> "Before"]

Write(i) ==
  /\ i \in Proc
  /\ pc[i] = "Before"
  /\ Reg' = [Reg EXCEPT ![i] = 1]
  /\ Res' = Res
  /\ pc'  = [pc  EXCEPT ![i] = "Between"]

Read(i) ==
  /\ i \in Proc
  /\ pc[i] = "Between"
  /\ Res' = [Res EXCEPT ![i] = Reg[Left(i)]]
  /\ Reg' = Reg
  /\ pc'  = [pc  EXCEPT ![i] = "Terminated"]

Next ==
  \E i \in Proc: Write(i) \/ Read(i)

(*
  Fair scheduling: each enabled Write(i) and Read(i) is weakly fair.
  This ensures that, under fair scheduling, all processes can eventually terminate.
*)
Fair ==
  /\ \A i \in Proc: WF_vars(Write(i))
  /\ \A i \in Proc: WF_vars(Read(i))

Spec == Init /\ [][Next]_vars /\ Fair

(*
  Type invariant: registers are Boolean (0 or 1), and control state is one of the three states.
*)
TypeInv ==
  /\ Reg \in [Proc -> {0, 1}]
  /\ Res \in [Proc -> {0, 1}]
  /\ pc  \in [Proc -> {"Before", "Between", "Terminated"}]

AllTerminated == \A i \in Proc: pc[i] = "Terminated"

(*
  Safety property: whenever every process has terminated, at least one result register equals 1.
*)
Safety == [](AllTerminated => (\E i \in Proc: Res[i] = 1))

(*
  Termination liveness under fair scheduling: it is possible (and under Fair, guaranteed)
  that all processes eventually reach the terminated state.
*)
Termination == <>AllTerminated

===============================================================================