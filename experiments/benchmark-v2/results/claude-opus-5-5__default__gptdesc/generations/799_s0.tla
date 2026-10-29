---------------------------- MODULE MCFindHighest ----------------------------
EXTENDS Sequences, Naturals, Integers, TLC

CONSTANTS MaxLength, MaxNat

ASSUME MaxLength \in Nat /\ MaxNat \in Nat

(***************************************************************************)
(* Model-checking helper operators                                         *)
(***************************************************************************)
BoundedNat == 0..MaxNat

BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..MaxLength }

(***************************************************************************)
(* The FindHighest algorithm being model checked                           *)
(***************************************************************************)
VARIABLES f, h, i, pc

vars == << f, h, i, pc >>

Init ==
    /\ f \in BoundedSeq(BoundedNat)
    /\ h = -1
    /\ i = 1
    /\ pc = "lb"

lb ==
    /\ pc = "lb"
    /\ IF i <= Len(f)
          THEN /\ h' = IF f[i] > h THEN f[i] ELSE h
               /\ i' = i + 1
               /\ pc' = "lb"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << h, i >>
    /\ UNCHANGED f

Terminating == pc = "Done" /\ UNCHANGED vars

Next == lb \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(lb)

(***************************************************************************)
(* State constraint bounding the explored behaviors                        *)
(***************************************************************************)
ConstraintLength == Len(f) <= MaxLength

(***************************************************************************)
(* Safety invariants                                                        *)
(***************************************************************************)
TypeOK ==
    /\ f \in Seq(BoundedNat)
    /\ i \in 1..(Len(f) + 1)
    /\ h \in BoundedNat \cup {-1}
    /\ pc \in {"lb", "Done"}

InductiveInvariant ==
    /\ \A idx \in 1..(i - 1) : f[idx] <= h
    /\ (i > 1 => \E idx \in 1..(i - 1) : f[idx] = h)
    /\ (i = 1 => h = -1)

Correctness ==
    pc = "Done" =>
        /\ \A idx \in DOMAIN f : f[idx] <= h
        /\ (Len(f) > 0 => \E idx \in DOMAIN f : f[idx] = h)
        /\ (Len(f) = 0 => h = -1)

(***************************************************************************)
(* Liveness                                                                 *)
(***************************************************************************)
Termination == <>(pc = "Done")

=============================================================================