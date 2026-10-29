---- MODULE FairCounter ----
EXTENDS Naturals

CONSTANT Max

ASSUME MaxIsNat == Max \in Nat /\ Max = 10

VARIABLES x, pc

vars == << x, pc >>

Init ==
    /\ x = 0
    /\ pc = "Loop"

Loop ==
    /\ pc = "Loop"
    /\ IF x < Max
         THEN /\ x' = x + 1
              /\ pc' = "Loop"
         ELSE /\ pc' = "Done"
              /\ x' = x

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Loop \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop)

TypeOK ==
    /\ x \in 0..Max
    /\ pc \in {"Loop", "Done"}

Bounded == x <= Max

DoneImpliesMax == (pc = "Done") => (x = Max)

UniqueAtFive == (x = 5) => (pc = "Loop")

UniqueAtNine == (x = 9) => (pc = "Loop")

NineEnablesTen == (x = 9 /\ pc = "Loop") => ENABLED (Loop /\ x' = Max)

Deterministic ==
    /\ (x < Max) => (pc = "Loop")
    /\ (pc = "Done") => (x = Max)

StepIsUnique ==
    [][ (pc = "Loop" /\ x < Max) => (x' = x + 1 /\ pc' = "Loop") ]_vars

Termination == <>(pc = "Done")

ReachesMax == <>(x = Max)

StaysDone == [](pc = "Done" => [](pc = "Done" /\ x = Max))

Progress == \A i \in 0..(Max - 1) : (x = i) ~> (x = i + 1)

====