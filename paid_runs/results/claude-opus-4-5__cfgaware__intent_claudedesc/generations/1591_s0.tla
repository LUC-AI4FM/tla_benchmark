---------------------------- MODULE MutualRecursion ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N

VARIABLES pc, stack, result, arg, oddEntryCount, evenToOddCount

vars == <<pc, stack, result, arg, oddEntryCount, evenToOddCount>>

Init ==
    /\ pc = "CallEvenMain"
    /\ stack = <<>>
    /\ result = FALSE
    /\ arg = N
    /\ oddEntryCount = 0
    /\ evenToOddCount = 0

CallEvenMain ==
    /\ pc = "CallEvenMain"
    /\ pc' = "Even"
    /\ arg' = N
    /\ stack' = Append(stack, <<"Main", 0>>)
    /\ UNCHANGED <<result, oddEntryCount, evenToOddCount>>

EvenProc ==
    /\ pc = "Even"
    /\ IF arg = 0
       THEN /\ result' = TRUE
            /\ pc' = "Return"
            /\ UNCHANGED <<arg, stack, oddEntryCount, evenToOddCount>>
       ELSE /\ arg' = arg - 1
            /\ stack' = Append(stack, <<"Even", arg>>)
            /\ pc' = "Odd"
            /\ oddEntryCount' = oddEntryCount + 1
            /\ evenToOddCount' = evenToOddCount + 1
            /\ UNCHANGED <<result>>

OddProc ==
    /\ pc = "Odd"
    /\ IF arg = 0
       THEN /\ result' = FALSE
            /\ pc' = "Return"
            /\ UNCHANGED <<arg, stack, oddEntryCount, evenToOddCount>>
       ELSE /\ arg' = arg - 1
            /\ stack' = Append(stack, <<"Odd", arg>>)
            /\ pc' = "Even"
            /\ UNCHANGED <<result, oddEntryCount, evenToOddCount>>

Return ==
    /\ pc = "Return"
    /\ Len(stack) > 0
    /\ LET top == stack[Len(stack)]
           caller == top[1]
       IN /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
          /\ IF caller = "Main"
             THEN pc' = "Print"
             ELSE pc' = "Return"
    /\ UNCHANGED <<result, arg, oddEntryCount, evenToOddCount>>

Print ==
    /\ pc = "Print"
    /\ pc' = "Done"
    /\ UNCHANGED <<stack, result, arg, oddEntryCount, evenToOddCount>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ CallEvenMain
    \/ EvenProc
    \/ OddProc
    \/ Return
    \/ Print
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

TypeOK ==
    /\ pc \in {"CallEvenMain", "Even", "Odd", "Return", "Print", "Done"}
    /\ result \in BOOLEAN
    /\ arg \in Nat
    /\ oddEntryCount \in Nat
    /\ evenToOddCount \in Nat

CorrectOddEntryCount ==
    pc = "Done" => oddEntryCount = 3

CorrectEvenToOddCount ==
    pc = "Done" => evenToOddCount = 3

CorrectResult ==
    pc = "Done" => result = TRUE

================================================================================