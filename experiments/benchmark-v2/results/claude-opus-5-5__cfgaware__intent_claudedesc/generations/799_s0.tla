---------------------------- MODULE FindHighest ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxLength, MaxNat

VARIABLES f, h, i, pc

vars == <<f, h, i, pc>>

(***************************************************************************)
(* Model-checking overrides for the infinite sets Nat and Seq(S).          *)
(***************************************************************************)
MCNat == 0 .. MaxNat

MCSeq(S) == UNION {[1 .. n -> S] : n \in 0 .. MaxLength}

Max(a, b) == IF a >= b THEN a ELSE b

(***************************************************************************)
(* Algorithm                                                               *)
(***************************************************************************)
Init ==
  /\ f \in Seq(Nat)
  /\ h = -1
  /\ i = 1
  /\ pc = "lb"

Loop ==
  /\ pc = "lb"
  /\ IF i <= Len(f)
       THEN /\ h' = Max(h, f[i])
            /\ i' = i + 1
            /\ pc' = "lb"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED <<h, i>>
  /\ UNCHANGED f

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == Loop \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop)

Termination == <>(pc = "Done")

(***************************************************************************)
(* Invariants and properties                                               *)
(***************************************************************************)
TypeOK ==
  /\ f \in Seq(Nat)
  /\ i \in 1 .. (Len(f) + 1)
  /\ i \in Nat
  /\ h \in Nat \cup {-1}
  /\ pc \in {"lb", "Done"}

InductiveInvariant ==
  /\ \A idx \in 1 .. (i - 1) : f[idx] <= h
  /\ (i = 1) => (h = -1)
  /\ (i > 1) => (\E idx \in 1 .. (i - 1) : f[idx] = h)

DoneIndexValue == pc = "Done" => i = Len(f) + 1

Correctness ==
  pc = "Done" =>
    /\ \A idx \in DOMAIN f : f[idx] <= h
    /\ (Len(f) > 0) => (\E idx \in DOMAIN f : f[idx] = h)
    /\ (Len(f) = 0) => (h = -1)

Progress == [][pc = "lb" /\ i <= Len(f) => i' = i + 1]_vars

MCConstraint == Len(f) <= MaxLength

=============================================================================