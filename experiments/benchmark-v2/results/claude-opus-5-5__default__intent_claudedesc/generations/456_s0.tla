---------------------------- MODULE ModularClock ----------------------------
(***************************************************************************)
(* A wrapper specification demonstrating modular composition through     *)
(* instantiation. The behavior of the system is defined in a reusable    *)
(* module (HourClock). This module instantiates that module, binding its *)
(* own local state variable `clock` to the parameter `hr` expected by     *)
(* the imported module. All initialization, transitions, fairness,       *)
(* safety, and liveness properties are inherited from the instance.      *)
(***************************************************************************)
EXTENDS Naturals

  --------------------------- MODULE HourClock ---------------------------
  (*************************************************************************)
  (* The reusable, externally specified behavior: a simple state machine *)
  (* modelling a 12-hour clock that advances one hour at a time.         *)
  (*************************************************************************)
  EXTENDS Naturals

  VARIABLE hr

  vars == << hr >>

  Hours == 1..12

  TypeOK == hr \in Hours

  Init == hr \in Hours

  Tick == hr' = IF hr = 12 THEN 1 ELSE hr + 1

  Next == Tick

  Spec == Init /\ [][Next]_vars /\ WF_vars(Tick)

  (* Safety: the clock always shows a valid hour. *)
  Safety == []TypeOK

  (* Liveness: the clock keeps ticking; every hour is shown infinitely often. *)
  Progress == \A h \in Hours : []<>(hr = h)
  =========================================================================