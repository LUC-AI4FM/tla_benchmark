---------------------------- MODULE MaxElement ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Tuples, minValue

ASSUME minValue \in Int

VARIABLES seq, i, max, pc

vars == <<seq, i, max, pc>>

IsElement(x, s) == \E k \in 1..Len(s) : s[k] = x

Init ==
    /\ seq \in Tuples
    /\ i = 1
    /\ max = minValue
    /\ pc = "check"

CheckPre ==
    /\ pc = "check"
    /\ Assert(\A n \in 1..Len(seq) : seq[n] > minValue,
              "Precondition violated: element not greater than minValue")
    /\ pc' = "loop"
    /\ UNCHANGED <<seq, i, max>>

Loop ==
    /\ pc = "loop"
    /\ IF i <= Len(seq)
         THEN /\ max' = IF seq[i] > max THEN seq[i] ELSE max
              /\ i' = i + 1
              /\ pc' = "loop"
         ELSE /\ pc' = "Done"
              /\ UNCHANGED <<i, max>>
    /\ UNCHANGED seq

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == CheckPre \/ Loop \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ seq \in Tuples
    /\ i \in Nat
    /\ max \in Int
    /\ pc \in {"check", "loop", "Done"}

Validity ==
    (pc = "Done" /\ Len(seq) > 0) => IsElement(max, seq)

Maximality ==
    (pc = "Done" /\ Len(seq) > 0) => \A n \in 1..Len(seq) : max >= seq[n]

EmptyHandling ==
    (pc = "Done" /\ Len(seq) = 0) => max = minValue

Correctness == Validity /\ Maximality /\ EmptyHandling

Termination == <>(pc = "Done")

=============================================================================