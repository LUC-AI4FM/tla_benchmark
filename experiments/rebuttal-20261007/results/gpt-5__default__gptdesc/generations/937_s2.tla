----------------------------- MODULE LiveHourClock -----------------------------

EXTENDS Naturals

VARIABLES hr

(*
  We assume an existing HourClock module that defines:
    - variable hr
    - Init: the initial-state predicate (typically hr \in 1..12)
    - HCnxt: the hour-tick next-state action
    - HC: the safety spec, usually Init /\ [][HCnxt]_hr
*)
INSTANCE HourClock WITH hr <- hr

Init  == HourClock!Init
HCnxt == HourClock!HCnxt
HC    == Init /\ [][HCnxt]_hr

(*
  Liveness-augmented specification: add weak fairness for HCnxt on hr.
*)
LSpec == HC /\ WF_hr(HCnxt)

(*
  Provide the customary names required by the prompt.
*)
Next == HCnxt
Spec == LSpec

(*
  Safety invariant: the typing condition of the initial state remains always true.
*)
TypeInv   == hr \in 1..12
AlwaysOK  == []TypeInv

(*
  Liveness properties:
    - ticking happens infinitely often
    - every hour value from 1 through 12 recurs infinitely often
*)
TickInf     == []<>(HCnxt)
AllHoursInf == \A i \in 1..12: []<>(hr = i)

(*
  Settling property and a concrete counterexample structure:
    - Settle says the clock eventually stabilizes forever at some hour.
    - CounterexampleStructure captures behaviors where ticks continue
      and all hours recur infinitely often, which refute Settle.
*)
Settle == \E h \in 1..12: <>([](hr = h))
CounterexampleStructure == /\ TickInf /\ AllHoursInf
Post == CounterexampleStructure => ~Settle

(*
  Theorems asserting the properties from LSpec.
  (No proofs provided; this module is intended to be SANY-parsable.)
*)
THEOREM FromLSpecInv ==
  LSpec => AlwaysOK

THEOREM FromLSpecLiveness ==
  LSpec => /\ TickInf
           /\ AllHoursInf

THEOREM FromLSpecPost ==
  LSpec => Post

=============================================================================