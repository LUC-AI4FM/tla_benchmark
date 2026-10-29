---------------------------- MODULE MCFindHighest ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS MaxLength, MaxNat

ASSUME MaxLength \in Nat
ASSUME MaxNat \in Nat

-----------------------------------------------------------------------------
(* Model-checking helper operators *)

NatOverride == 0..MaxNat

SeqOf(set, count) == UNION { [1..m -> set] : m \in 0..count }

BoundedSeq(S) == SeqOf(S, MaxLength)

-----------------------------------------------------------------------------
(* Embedded FindHighest behavior, over the bounded model *)

VARIABLES f, h, i, pc

vars == << f, h, i, pc >>

Range(s) == { s[k] : k \in DOMAIN s }

Max(a, b) == IF a > b THEN a ELSE b

StateConstraint == Len(f) <= MaxLength

Init ==
    /\ f \in BoundedSeq(NatOverride)
    /\ h = -1
    /\ i = 1
    /\ pc = "lb"

Loop ==
    /\ pc = "lb"
    /\ IF i <= Len(f)
          THEN /\ h' = Max(f[i], h)
               /\ i' = i + 1
               /\ pc' = "lb"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << h, i >>
    /\ UNCHANGED f

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Loop \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ f \in BoundedSeq(NatOverride)
    /\ i \in 1..(Len(f) + 1)
    /\ h \in NatOverride \cup {-1}
    /\ pc \in {"lb", "Done"}

InductiveInvariant ==
    /\ \A k \in 1..(i - 1) : h >= f[k]
    /\ (i = 1) => (h = -1)
    /\ (i > 1) => (\E k \in 1..(i - 1) : h = f[k])

PartialCorrectness ==
    pc = "Done" =>
        /\ Len(f) = 0 => h = -1
        /\ Len(f) > 0 =>
              /\ h \in Range(f)
              /\ \A k \in DOMAIN f : h >= f[k]

-----------------------------------------------------------------------------
(* Liveness property *)

Termination == <>(pc = "Done")

=============================================================================