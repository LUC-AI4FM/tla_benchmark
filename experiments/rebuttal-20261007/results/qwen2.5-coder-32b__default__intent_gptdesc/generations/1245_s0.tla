------------------------------- MODULE Translator -------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    AST,  \* Abstract Syntax Tree of the algorithm
    Labels, \* Set of all labels in the AST
    Procedures, \* Set of all procedure names in the AST
    GlobalVars, \* Set of all global variable names in the AST
    LocalVars \* Mapping from procedure names to sets of local variable names

VARIABLES 
    State, \* Current state of the algorithm execution
    Stack, \* Call stack for procedure calls
    Processes, \* Mapping from process IDs to their states
    NextLabel, \* Next label to execute in each process
    EnabledActions \* Set of enabled actions in the current state

Init == 
    /\ State = [g \in GlobalVars |-> UNCHANGED]
    /\ Stack = << >>
    /\ Processes = [p \in 1..Cardinality(Labels) |-> [l \in Labels |-> FALSE]]
    /\ NextLabel = [p \in 1..Cardinality(Labels) |-> "start"]
    /\ EnabledActions = {}

Next == 
    \/ \E p \in DOMAIN Processes, l \in Labels : 
        \/ \* Handle if/then/else
           (NextLabel[p] = l /\ AST[l]["type"] = "if" /\ AST[l]["condition"] \in State)
        \/ \* Handle either/when/with
           (NextLabel[p] = l /\ AST[l]["type"] = "either" /\ EnabledActions /= {})
        \/ \* Handle while loop
           (NextLabel[p] = l /\ AST[l]["type"] = "while" /\ AST[l]["condition"] \in State)
        \/ \* Handle call/return
           (NextLabel[p] = l /\ AST[l]["type"] = "call")
        \/ \* Handle goto
           (NextLabel[p] = l /\ AST[l]["type"] = "goto")
        \/ \* Handle labeled statements
           (NextLabel[p] = l /\ AST[l]["type"] = "labeled" /\ EnabledActions /= {})
    \/ \E p \in DOMAIN Processes, a \in EnabledActions :
        \/ \* Execute enabled action
           (a["type"] = "assign" /\ State' = [State EXCEPT ![a["var"]] = a["value"]])
        \/ \* Push procedure call onto stack
           (a["type"] = "call" /\ Stack' = Append(Stack, <<p, NextLabel[p]>>))
        \/ \* Pop procedure return from stack
           (a["type"] = "return" /\ LET top == Head(Stack) IN
                Stack' = Tail(Stack) /\ NextLabel' = [NextLabel EXCEPT ![top[1]] = top[2]])
        \/ \* Update next label for process
           (a["type"] = "goto" /\ NextLabel' = [NextLabel EXCEPT ![p] = a["label"]])

Spec == Init /\ [][Next]_<<State, Stack, Processes, NextLabel, EnabledActions>>

\* Safety invariants
Safety ==
    /\ \A p \in DOMAIN Processes : NextLabel[p] \in Labels
    /\ \A p \in DOMAIN Processes, l \in Labels : Processes[p][l] => l \in Labels
    /\ \A p1, p2 \in DOMAIN Processes, v \in GlobalVars : p1 # p2 => State[p1][v] = State[p2][v]
    /\ \A p \in DOMAIN Processes, l \in Labels : AST[l]["type"] = "if" => AST[l]["condition"] \subseteq DOMAIN State
    /\ \A p \in DOMAIN Processes, l \in Labels : AST[l]["type"] = "while" => AST[l]["condition"] \subseteq DOMAIN State

\* Liveness properties
Liveness ==
    \/ \E p \in DOMAIN Processes, l \in Labels : AST[l]["type"] = "if" => <>[](NextLabel[p] = l => EnabledActions /= {})
    \/ \E p \in DOMAIN Processes, l \in Labels : AST[l]["type"] = "either" => <>[](NextLabel[p] = l => EnabledActions /= {})
    \/ \E p \in DOMAIN Processes, l \in Labels : AST[l]["type"] = "while" => <>[](NextLabel[p] = l => EnabledActions /= {})

\* Fairness conditions
Fairness ==
    WF_next(<<State, Stack, Processes, NextLabel, EnabledActions>>)

=============================================================================