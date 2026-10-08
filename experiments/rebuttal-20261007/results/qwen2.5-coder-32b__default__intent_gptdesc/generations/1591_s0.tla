------------------------------- MODULE ParityCheck -------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N

VARIABLES callStack, result

Init == 
  /\ callStack = <<>>
  /\ result = FALSE

Next ==
  \/ \E args \in SUBSET Nat : 
      /\ callStack = <<>>
      /\ args = {N}
      /\ UNCHANGED result
      /\ callStack' = <<args>>
  \/ \E top \in Seq(Nat) :
      /\ Len(callStack) > 0
      /\ callStack = <<top>> \o rest
      /\ LET n == Head(top)
         IN n > 0
            /\ callStack' = <<{n - 1}>>
                         \o <<top>>
                         \o rest
            /\ UNCHANGED result
  \/ \E top \in Seq(Nat) :
      /\ Len(callStack) > 0
      /\ callStack = <<top>> \o rest
      /\ LET n == Head(top)
         IN n = 0
            /\ callStack' = rest
            /\ result' = (n % 2 = 0)

Spec ==
  Init /\ [][Next]_<<callStack, result>>

\* Invariants
Inv1 == \A args \in SUBSET Nat : 
          \/ args = {}
          \/ Len(args) = 1

Inv2 == \/ callStack = <<>>
        \/ Len(callStack) > 0

Inv3 == \/ callStack = <<>>
        \/ LET top == Head(callStack)
           IN Len(top) = 1

\* Liveness
Termination ==
  <>(callStack = <<>>)

FunctionalCorrectness ==
  [](callStack = <<>> => result = (N % 2 = 0))

SafetyProperties ==
  Inv1 /\ Inv2 /\ Inv3

LivenessProperties ==
  Termination /\ FunctionalCorrectness

CompleteSpec ==
  Spec /\ SafetyProperties /\ LivenessProperties

=============================================================================