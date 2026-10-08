------------------------------- MODULE Bakery --------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumProcesses
ASSUME NumProcesses \in Nat /\ NumProcesses > 0

VARIABLES 
    choosing,     \* Choosing flags for each process
    ticketNum,    \* Ticket numbers assigned to processes
    localMax,     \* Local maximum ticket number read by each process
    nextProc,     \* Next process examined by each process
    controlLoc,   \* Control location of each process

vars == <<choosing, ticketNum, localMax, nextProc, controlLoc>>

Init == 
    /\ choosing = [p \in 1..NumProcesses -> FALSE]
    /\ ticketNum = [p \in 1..NumProcesses -> 0]
    /\ localMax = [p \in 1..NumProcesses -> 0]
    /\ nextProc = [p \in 1..NumProcesses -> 1]
    /\ controlLoc = [p \in 1..NumProcesses -> "entry"]

Next == 
    \/ \E p \in 1..NumProcesses : 
        (controlLoc[p] = "entry" 
         /\ choosing' = [choosing EXCEPT ![p] = TRUE]
         /\ localMax' = [localMax EXCEPT ![p] = Max({ticketNum[q] | q \in 1..NumProcesses})]
         /\ ticketNum' = [ticketNum EXCEPT ![p] = localMax[p] + 1]
         /\ choosing' = [choosing' EXCEPT ![p] = FALSE]
         /\ nextProc' = [nextProc EXCEPT ![p] = 1]
         /\ controlLoc' = [controlLoc EXCEPT ![p] = "request"])
    \/ \E p \in 1..NumProcesses : 
        (controlLoc[p] = "request" 
         /\ LET q == nextProc[p]
            IN
                \/ q > NumProcesses -> 
                    (nextProc' = [nextProc EXCEPT ![p] = 1]
                     /\ controlLoc' = [controlLoc EXCEPT ![p] = "critical"])
                \/ choosing[q] \/ (ticketNum[q] # 0) /\ (ticketNum[q] < ticketNum[p]) \/ (ticketNum[q] = ticketNum[p] /\ q < p) -> 
                    nextProc' = [nextProc EXCEPT ![p] = q + 1]
    \/ \E p \in 1..NumProcesses : 
        (controlLoc[p] = "critical" 
         /\ controlLoc' = [controlLoc EXCEPT ![p] = "release"])
    \/ \E p \in 1..NumProcesses : 
        (controlLoc[p] = "release" 
         /\ ticketNum' = [ticketNum EXCEPT ![p] = 0]
         /\ controlLoc' = [controlLoc EXCEPT ![p] = "entry"])

Spec == Init /\ [][Next]_<<vars>>

\* Invariants
MutualExclusion ==
    \A p, q \in 1..NumProcesses : 
        (controlLoc[p] = "critical") => ~(q # p) \/ (controlLoc[q] # "critical")

\* State constraint for TLC model checking
TicketBound ==
    \A p \in 1..NumProcesses :
        ticketNum[p] <= NumProcesses

Invariants == MutualExclusion /\ TicketBound

Liveness ==
    []<>(\E p \in 1..NumProcesses : controlLoc[p] = "critical")

Fairness ==
    WF_vars(Next)

THEOREM Spec => Invariants
THEOREM Spec, Fairness => Liveness

=============================================================================