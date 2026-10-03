----------------------------- MODULE Bakery -----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS N          \* The number of processes
CONSTANTS MaxTicket  \* An upper bound on ticket numbers for model checking

ASSUME N \in 1..MaxTicket

Procs == 1..N

\* The state variables of the algorithm.
VARIABLES pc,       \* The program counter for each process
          choosing, \* choosing[i] is TRUE iff process i is choosing a ticket
          ticket    \* ticket[i] is the ticket number for process i

vars == <<pc, choosing, ticket>>

\* Define the set of possible states for the program counter.
PCStates == {"NonCritical", "Choosing", "Waiting", "Critical"}

\* Type invariant to ensure variables have the expected types and values.
TypeOK ==
    /\ pc \in [Procs -> PCStates]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ ticket \in [Procs -> 0..MaxTicket]

\* The initial state of the system.
Init ==
    /\ pc = [p \in Procs |-> "NonCritical"]
    /\ choosing = [p \in Procs |-> FALSE]
    /\ ticket = [p \in Procs |-> 0]

\*=============================================================================