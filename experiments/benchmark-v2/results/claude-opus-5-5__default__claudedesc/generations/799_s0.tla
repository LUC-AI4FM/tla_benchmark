---------------------------- MODULE MCFindHighest ----------------------------
(***************************************************************************)
(* Model-checking configuration for the FindHighest algorithm. The         *)
(* algorithm is defined inline (instead of using EXTENDS FindHighest) so   *)
(* that the module parses on its own. Nat is replaced by the finite set    *)
(* MCNat, and Seq by the finite constructor MCSeq.                         *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

CONSTANTS MaxLength, MaxNat

ASSUME MaxLength \in Nat
ASSUME MaxNat \in Nat

(***************************************************************************)
(* Finite substitutes for infinite sets                                    *)
(***************************************************************************)
MCNat == 0 .. MaxNat

MCSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. MaxLength }

(***************************************************************************)
(* FindHighest algorithm                                                   *)
(***************************************************************************)
VARIABLES f, h, i, pc

vars == << f, h, i, pc >>

max(a, b) == IF a >= b THEN a ELSE b

Init ==
    /\ f \in MCSeq(MCNat)
    /\ h = -1
    /\ i = 1
    /\ pc = "lb"

lb ==
    /\ pc = "lb"
    /\ IF i <= Len(f)
          THEN /\ h' = max(h, f[i])
               /\ i' = i + 1
               /\ pc' = "lb"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << h, i >>
    /\ f' = f

Terminating == pc = "Done" /\ UNCHANGED vars

Next == lb \/ Terminating

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* State constraint                                                        *)
(***************************************************************************)
MCConstraint == Len(f) <= MaxLength

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
    /\ f \in MCSeq(MCNat)
    /\ i \in 1 .. (Len(f) + 1)
    /\ h \in MCNat \cup {-1}
    /\ pc \in {"lb", "Done"}

InductiveInvariant ==
    /\ TypeOK
    /\ \A idx \in 1 .. (i - 1) : f[idx] <= h
    /\ (i = 1) => (h = -1)
    /\ (i > 1) => \E idx \in 1 .. (i - 1) : f[idx] = h

DoneIndexValue == pc = "Done" => i = Len(f) + 1

Correctness ==
    pc = "Done" =>
        /\ \A idx \in DOMAIN f : f[idx] <= h
        /\ (Len(f) > 0) => \E idx \in DOMAIN f : f[idx] = h
        /\ (Len(f) = 0) => h = -1

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)
Termination == <>(pc = "Done")

(***************************************************************************)
(* Model values: MaxLength = 3, MaxNat = 4                                  *)
(***************************************************************************)
MCMaxLength == 3
MCMaxNat == 4

=============================================================================