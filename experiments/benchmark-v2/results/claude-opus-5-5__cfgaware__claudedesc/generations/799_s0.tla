---------------------------- MODULE MCFindHighest ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS MaxLength, MaxNat

ASSUME MaxLength \in Nat
ASSUME MaxNat \in Nat

\* ---------------------------------------------------------------------------
\* FindHighest algorithm: scans a sequence f and records the highest value in h
\* ---------------------------------------------------------------------------

VARIABLES f, h, i, pc

vars == <<f, h, i, pc>>

Max(a, b) == IF a >= b THEN a ELSE b

Init ==
    /\ f \in Seq(Nat)
    /\ h = -1
    /\ i = 1
    /\ pc = "lb"

lb ==
    /\ pc = "lb"
    /\ IF i <= Len(f)
          THEN /\ h' = Max(h, f[i])
               /\ i' = i + 1
               /\ pc' = "lb"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED <<h, i>>
    /\ UNCHANGED f

Terminating == pc = "Done" /\ UNCHANGED vars

Next == lb \/ Terminating

Spec == Init /\ [][Next]_vars

\* ---------------------------------------------------------------------------
\* Properties
\* ---------------------------------------------------------------------------

TypeOK ==
    /\ f \in Seq(Nat)
    /\ i \in 1..(Len(f) + 1)
    /\ h \in Nat \cup {-1}
    /\ pc \in {"lb", "Done"}

InductiveInvariant ==
    /\ TypeOK
    /\ \A idx \in 1..(i - 1) : f[idx] <= h
    /\ (h = -1) <=> (i = 1)
    /\ h # -1 => \E idx \in 1..(i - 1) : f[idx] = h
    /\ pc = "Done" => i = Len(f) + 1

DoneIndexValue == pc = "Done" => i = Len(f) + 1

Correctness ==
    pc = "Done" =>
        /\ \A idx \in DOMAIN f : f[idx] <= h
        /\ (Len(f) = 0 => h = -1)
        /\ (Len(f) > 0 => \E idx \in DOMAIN f : f[idx] = h)

\* ---------------------------------------------------------------------------
\* Model-checking overrides
\* ---------------------------------------------------------------------------

MCNat == 0..MaxNat

MCSeq(S) == UNION {[1..n -> S] : n \in 0..MaxLength}

MCConstraint == Len(f) <= MaxLength

=============================================================================