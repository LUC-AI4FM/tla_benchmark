------------------------------- MODULE PlusCalToTLA --------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    -- Define any constants here that are necessary for the specification
    ALGORITHM_NAME,
    PROCEDURES,
    PROCESSES,
    LABELS

VARIABLES 
    ast,          \* Abstract Syntax Tree
    lexemes,      \* Lexeme sequence representing TLA+ output
    processStates,\* States of each process
    labels        \* Labels in the algorithm

Init == 
    /\ ast = [algorithmName |-> ALGORITHM_NAME, procedures |-> PROCEDURES, processes |-> PROCESSES, labels |-> LABELS]
    /\ lexemes = <<>>
    /\ processStates = [p \in PROCESSES |-> "init"]
    /\ labels = [l \in LABELS |-> FALSE]

Next ==
    \/ \E p \in PROCESSES : ProcessAction(p)
    \/ NextStep
    \/ Termination

ProcessAction(p) ==
    LET action == ast.processes[p].action IN
        /\ processStates' = [processStates EXCEPT ![p] = action]
        /\ lexemes' = AppendLexeme(lexemes, action)

NextStep ==
    /\ \E l \in LABELS : labels[l]
    /\ lexemes' = AppendLexeme(lexemes, "NEXT")

Termination ==
    /\ \A p \in PROCESSES : processStates[p] = "done"
    /\ lexemes' = AppendLexeme(lexemes, "TERMINATION")

AppendLexeme(seq, elem) ==
    seq \o <<elem>>

Spec == Init /\ [][Next]_<<ast, lexemes, processStates, labels>> 

Fairness ==
    WF_next(ProcessAction)
    \/ WF_next(NextStep)
    \/ SF_next(ProcessAction)

THEOREM Spec => []<>(\A p \in PROCESSES : processStates[p] = "done")

=============================================================================