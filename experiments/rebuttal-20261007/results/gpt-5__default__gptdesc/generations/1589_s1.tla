---- MODULE Euclid ----
EXTENDS Integers, TLC

CONSTANT MaxNum

ASSUME MaxNum \in Nat \ {0}

(*
--algorithm Euclid
variables
  u_ini \in 1..MaxNum,
  v_ini \in 1..MaxNum,
  u = u_ini,
  v = v_ini;

begin
  Loop:
    while u # v do
      if u > v then
        u := u - v;
      else
        v := v - u;
      end if;
    end while;

  Done:
    skip;
end algorithm;
*)

(***************************************************************************)
(* TLA+ translation of the PlusCal algorithm above                         *)
(***************************************************************************)

VARIABLES u_ini, v_ini, u, v, pc

vars == << u_ini, v_ini, u, v, pc >>

RECURSIVE GCD(_,_)
GCD(a, b) == IF b = 0 THEN a ELSE GCD(b, a % b)

Init ==
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u = u_ini
  /\ v = v_ini
  /\ pc = "Loop"

DecU ==
  /\ pc = "Loop"
  /\ u # v
  /\ u > v
  /\ u' = u - v
  /\ v' = v
  /\ pc' = "Loop"
  /\ UNCHANGED << u_ini, v_ini >>

DecV ==
  /\ pc = "Loop"
  /\ u # v
  /\ u <= v
  /\ v' = v - u
  /\ u' = u
  /\ pc' = "Loop"
  /\ UNCHANGED << u_ini, v_ini >>

DoneAction ==
  /\ pc = "Loop"
  /\ u = v
  /\ pc' = "Done"
  /\ UNCHANGED << u_ini, v_ini, u, v >>

Next == DecU \/ DecV \/ DoneAction

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

TypeInv ==
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u \in 1..MaxNum
  /\ v \in 1..MaxNum
  /\ pc \in {"Loop", "Done"}

GCDInvariant ==
  GCD(u, v) = GCD(u_ini, v_ini)

Safety == TypeInv /\ GCDInvariant

(***************************************************************************)
(* Liveness and correctness properties                                     *)
(***************************************************************************)

Termination ==
  <> (pc = "Done")

Correctness ==
  (pc = "Done") => /\ u = v /\ u = GCD(u_ini, v_ini)

(***************************************************************************)
(* TLC-based counting "covers" for named properties.                       *)
(* Include these as INVARIANTS or PROPERTIES in your TLC model to get      *)
(* printed counts indicating how many reached states satisfy them.         *)
(***************************************************************************)

Cover_Termination ==
  /\ pc = "Done"
  /\ PrintT("COVER: Termination reached")

Cover_Correctness ==
  /\ (pc = "Done") /\ (u = GCD(u_ini, v_ini))
  /\ PrintT("COVER: Correct result")

====