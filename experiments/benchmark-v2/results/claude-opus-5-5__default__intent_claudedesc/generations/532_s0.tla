---- MODULE IntegerExponentiation ----
EXTENDS Integers, Naturals, TLC

CONSTANTS Bases, Exponents

ASSUME BasesAreIntegers == Bases \subseteq Int
ASSUME ExponentsAreNats == Exponents \subseteq Nat

VARIABLES base, exp, result, count, pc

vars == << base, exp, result, count, pc >>

RECURSIVE Pow(_, _)
Pow(b, e) == IF e = 0 THEN 1 ELSE b * Pow(b, e - 1)

Init ==
    /\ base \in Bases
    /\ exp \in Exponents
    /\ result = 1
    /\ count = 0
    /\ pc = "loop"

Loop ==
    /\ pc = "loop"
    /\ IF count < exp
          THEN /\ result' = result * base
               /\ count' = count + 1
               /\ pc' = "loop"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << result, count >>
    /\ UNCHANGED << base, exp >>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Loop \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ base \in Int
    /\ exp \in Nat
    /\ result \in Int
    /\ count \in Nat
    /\ pc \in {"loop", "Done"}

InputConstraints ==
    /\ base \in Int
    /\ exp \in Nat

LoopInvariant ==
    /\ count <= exp
    /\ result = Pow(base, count)

PartialCorrectness ==
    (pc = "Done") => (result = Pow(base, exp))

Termination == <>(pc = "Done")

====