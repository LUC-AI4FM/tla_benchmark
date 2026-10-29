---------------------------- MODULE MCFindHighest ----------------------------
EXTENDS Integers, Sequences

CONSTANTS MaxLength, MaxNat

VARIABLES f, h, i, pc

vars == <<f, h, i, pc>>

-----------------------------------------------------------------------------
(* The FindHighest algorithm: scan sequence f, recording highest value in h *)

Init ==
  /\ f \in Seq(Nat)
  /\ h = -1
  /\ i = 1
  /\ pc = "lb"

Loop ==
  /\ pc = "lb"
  /\ IF i <= Len(f)
       THEN /\ i' = i + 1
            /\ h' = IF f[i] > h THEN f[i] ELSE h
            /\ pc' = pc
       ELSE /\ pc' = "Done"
            /\ UNCHANGED <<i, h>>
  /\ UNCHANGED f

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == Loop \/ Terminating

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
  /\ f \in Seq(Nat)
  /\ i \in 1 .. (Len(f) + 1)
  /\ h \in Nat \cup {-1}
  /\ pc \in {"lb", "Done"}

InductiveInvariant ==
  /\ TypeOK
  /\ \A idx \in 1 .. (i - 1) : f[idx] <= h
  /\ (i = 1 => h = -1)
  /\ (i > 1 => \E idx \in 1 .. (i - 1) : f[idx] = h)
  /\ (pc = "Done" => i = Len(f) + 1)

DoneIndexValue == pc = "Done" => i = Len(f) + 1

Correctness ==
  pc = "Done" =>
    /\ \A idx \in DOMAIN f : f[idx] <= h
    /\ (Len(f) = 0 => h = -1)
    /\ (Len(f) > 0 => \E idx \in DOMAIN f : f[idx] = h)

-----------------------------------------------------------------------------
(* Model-checking helpers *)

MCConstraint == Len(f) <= MaxLength

MCNat == 0 .. MaxNat

MCSeq(S) == UNION {[1 .. n -> S] : n \in 0 .. MaxLength}

=============================================================================