---------------------------- MODULE EvenOdd ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N

VARIABLES pc, stack, result, arg, evenEntryCount, oddEntryCount, evenToOddCount

vars == <<pc, stack, result, arg, evenEntryCount, oddEntryCount, evenToOddCount>>

TypeOK ==
    /\ pc \in {"main", "call_even", "even_check", "call_odd_from_even", "return_from_odd_to_even",
               "odd_check", "call_even_from_odd", "return_from_even_to_odd", "return", "print", "done"}
    /\ stack \in Seq([proc: {"even", "odd"}, arg: Nat])
    /\ result \in BOOLEAN \union {-1}
    /\ arg \in Nat
    /\ evenEntryCount \in Nat
    /\ oddEntryCount \in Nat
    /\ evenToOddCount \in Nat

Init ==
    /\ pc = "main"
    /\ stack = <<>>
    /\ result = -1
    /\ arg = 0
    /\ evenEntryCount = 0
    /\ oddEntryCount = 0
    /\ evenToOddCount = 0

Main ==
    /\ pc = "main"
    /\ pc' = "call_even"
    /\ arg' = N
    /\ stack' = <<[proc |-> "main", arg |-> N]>> \o stack
    /\ evenEntryCount' = evenEntryCount + 1
    /\ UNCHANGED <<result, oddEntryCount, evenToOddCount>>

EvenCheck ==
    /\ pc = "even_check"
    /\ IF arg = 0
       THEN /\ result' = TRUE
            /\ pc' = "return"
            /\ UNCHANGED <<arg, evenEntryCount, oddEntryCount, evenToOddCount>>
       ELSE /\ arg' = arg - 1
            /\ pc' = "call_odd_from_even"
            /\ oddEntryCount' = oddEntryCount + 1
            /\ evenToOddCount' = evenToOddCount + 1
            /\ UNCHANGED <<result, evenEntryCount>>
    /\ UNCHANGED stack

CallEven ==
    /\ pc = "call_even"
    /\ pc' = "even_check"
    /\ UNCHANGED <<stack, result, arg, evenEntryCount, oddEntryCount, evenToOddCount>>

CallOddFromEven ==
    /\ pc = "call_odd_from_even"
    /\ stack' = <<[proc |-> "even", arg |-> arg + 1]>> \o stack
    /\ pc' = "odd_check"
    /\ UNCHANGED <<result, arg, evenEntryCount, oddEntryCount, evenToOddCount>>

OddCheck ==
    /\ pc = "odd_check"
    /\ IF arg = 0
       THEN /\ result' = FALSE
            /\ pc' = "return"
            /\ UNCHANGED <<arg, evenEntryCount, oddEntryCount, evenToOddCount>>
       ELSE /\ arg' = arg - 1
            /\ pc' = "call_even_from_odd"
            /\ evenEntryCount' = evenEntryCount + 1
            /\ UNCHANGED <<result, oddEntryCount, evenToOddCount>>
    /\ UNCHANGED stack

CallEvenFromOdd ==
    /\ pc = "call_even_from_odd"
    /\ stack' = <<[proc |-> "odd", arg |-> arg + 1]>> \o stack
    /\ pc' = "even_check"
    /\ UNCHANGED <<result, arg, evenEntryCount, oddEntryCount, evenToOddCount>>

Return ==
    /\ pc = "return"
    /\ stack # <<>>
    /\ LET top == Head(stack)
       IN IF top.proc = "main"
          THEN /\ pc' = "print"
               /\ stack' = Tail(stack)
          ELSE IF top.proc = "even"
               THEN /\ pc' = "return_from_odd_to_even"
                    /\ stack' = Tail(stack)
               ELSE /\ pc' = "return_from_even_to_odd"
                    /\ stack' = Tail(stack)
    /\ UNCHANGED <<result, arg, evenEntryCount, oddEntryCount, evenToOddCount>>

ReturnFromOddToEven ==
    /\ pc = "return_from_odd_to_even"
    /\ pc' = "return"
    /\ UNCHANGED <<stack, result, arg, evenEntryCount, oddEntryCount, evenToOddCount>>

ReturnFromEvenToOdd ==
    /\ pc = "return_from_even_to_odd"
    /\ pc' = "return"
    /\ UNCHANGED <<stack, result, arg, evenEntryCount, oddEntryCount, evenToOddCount>>

Print ==
    /\ pc = "print"
    /\ pc' = "done"
    /\ UNCHANGED <<stack, result, arg, evenEntryCount, oddEntryCount, evenToOddCount>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ Main
    \/ CallEven
    \/ EvenCheck
    \/ CallOddFromEven
    \/ OddCheck
    \/ CallEvenFromOdd
    \/ Return
    \/ ReturnFromOddToEven
    \/ ReturnFromEvenToOdd
    \/ Print
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "done")

CorrectResult == pc = "done" => (result = (N % 2 = 0))

OddEntryCountBounded == oddEntryCount <= N \div 2 + 1

EvenToOddCountBounded == evenToOddCount <= N \div 2 + 1

OddEntryCountCorrectAtEnd == pc = "done" => oddEntryCount = N \div 2

EvenToOddCountCorrectAtEnd == pc = "done" => evenToOddCount = N \div 2

CountsMatchAtEnd == pc = "done" => (oddEntryCount = 3 /\ evenToOddCount = 3)

SafetyInvariant ==
    /\ TypeOK
    /\ CorrectResult
    /\ OddEntryCountBounded
    /\ EvenToOddCountBounded
    /\ CountsMatchAtEnd

=============================================================================