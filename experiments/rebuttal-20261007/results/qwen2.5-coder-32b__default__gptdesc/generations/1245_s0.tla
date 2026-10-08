------------------------------- MODULE PlusCalToTLAPlus ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, Records

CONSTANTS 
    -- Define any necessary constants here
    ProcessActions,
    Statements,
    Variables

VARIABLES 
    ast,          \* Abstract Syntax Tree
    translatedAst,\* Translated Abstract Syntax Tree
    processState  \* State of each process

Init == 
    /\ ast = [p \in Processes |-> << >>]   \* Initial AST is empty for all processes
    /\ translatedAst = [p \in Processes |-> << >>]
    /\ processState = [p \in Processes |-> "init"]

Next ==
    \/ \E p \in Processes : ProcessAction(p)
    \/ TranslateCallsReturnsGotos
    \/ AddSubscriptsForLocalVariables
    \/ ConstructInitNextSpecTermination

ProcessAction(p) ==
    LET action == CHOOSE a \in ProcessActions : TRUE
    IN /\ processState[p] = "running"
       /\ translatedAst' = [translatedAst EXCEPT ![p] = Append(translatedAst[p], action)]
       /\ UNCHANGED <<ast, processState>>

TranslateCallsReturnsGotos ==
    /\ ast' = Translate(ast)
    /\ UNCHANGED <<translatedAst, processState>>

AddSubscriptsForLocalVariables ==
    /\ translatedAst' = AddSubscripts(translatedAst)
    /\ UNCHANGED <<ast, processState>>

ConstructInitNextSpecTermination ==
    /\ Init == [p \in Processes |-> CHOOSE i \in Statements : TRUE]
    /\ Next == [p \in Processes |-> CHOOSE n \in Statements : TRUE]
    /\ Spec == Init /\ [][Next]_<<p \in Processes >> /\ WF_next(<<p \in Processes >>)
    /\ Termination == <>(\A p \in Processes : processState[p] = "terminated")
    /\ UNCHANGED <<ast, translatedAst>>

Spec ==
    /\ Init
    /\ SpecFairness
    /\ []Next

SpecFairness ==
    \/ WeakFairnessProcessActions
    \/ WeakFairnessNext
    \/ StrongFairnessProcessActions

WeakFairnessProcessActions ==
    WF_next(ProcessActions)

WeakFairnessNext ==
    WF_next(<<p \in Processes >>)

StrongFairnessProcessActions ==
    SF_next(ProcessActions)

=============================================================================