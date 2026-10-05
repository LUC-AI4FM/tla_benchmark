---------------------------- MODULE ByzantineConsensus ----------------------------
EXTENDS Integers, FiniteSets, Naturals

CONSTANTS N, T, F

ASSUME /\ N \in Nat \ {0}
       /\ T \in Nat
       /\ F \in Nat
       /\ F <= T
       /\ N > 3 * T

Procs == 1..N

Values == {0, 1}

VARIABLES
    procState,      \* procState[p] \in {"init", "proposed", "decided"}
    proposal,       \* proposal[p] \in {0, 1} - initial value of process p
    decision,       \* decision[p] \in {0, 1, "undecided", "none"}
    byzantine,      \* byzantine[p] \in BOOLEAN - whether process p is Byzantine
    msgCount0,      \* msgCount0[p] - count of "0" messages received by p from correct processes
    msgCount1,      \* msgCount1[p] - count of "1" messages received by p from correct processes
    byzMsgCount0,   \* byzMsgCount0[p] - count of "0" messages received by p from Byzantine processes
    byzMsgCount1,   \* byzMsgCount1[p] - count of "1" messages received by p from Byzantine processes
    proposed,       \* proposed[p] \in BOOLEAN - whether correct process p has broadcast its value
    numByzantine    \* current number of Byzantine processes

vars == <<procState, proposal, decision, byzantine, msgCount0, msgCount1, 
          byzMsgCount0, byzMsgCount1, proposed, numByzantine>>

TypeOK ==
    /\ procState \in [Procs -> {"init", "proposed", "decided"}]
    /\ proposal \in [Procs -> Values]
    /\ decision \in [Procs -> {0, 1, "undecided", "none"}]
    /\ byzantine \in [Procs -> BOOLEAN]
    /\ msgCount0 \in [Procs -> 0..N]
    /\ msgCount1 \in [Procs -> 0..N]
    /\ byzMsgCount0 \in [Procs -> 0..N]
    /\ byzMsgCount1 \in [Procs -> 0..N]
    /\ proposed \in [Procs -> BOOLEAN]
    /\ numByzantine \in 0..N

CorrectProcs == {p \in Procs : ~byzantine[p]}
ByzantineProcs == {p \in Procs : byzantine[p]}

Init ==
    /\ procState = [p \in Procs |-> "init"]
    /\ proposal \in [Procs -> Values]
    /\ decision = [p \in Procs |-> "none"]
    /\ byzantine = [p \in Procs |-> FALSE]
    /\ msgCount0 = [p \in Procs |-> 0]
    /\ msgCount1 = [p \in Procs |-> 0]
    /\ byzMsgCount0 = [p \in Procs |-> 0]
    /\ byzMsgCount1 = [p \in Procs |-> 0]
    /\ proposed = [p \in Procs |-> FALSE]
    /\ numByzantine = 0

\* A correct process broadcasts its proposal
Propose(p) ==
    /\ ~byzantine[p]
    /\ procState[p] = "init"
    /\ ~proposed[p]
    /\ proposed' = [proposed EXCEPT ![p] = TRUE]
    /\ procState' = [procState EXCEPT ![p] = "proposed"]
    \* All other correct processes receive this message
    /\ msgCount0' = [q \in Procs |-> 
                        IF proposal[p] = 0 
                        THEN msgCount0[q] + 1 
                        ELSE msgCount0[q]]
    /\ msgCount1' = [q \in Procs |-> 
                        IF proposal[p] = 1 
                        THEN msgCount1[q] + 1 
                        ELSE msgCount1[q]]
    /\ UNCHANGED <<proposal, decision, byzantine, byzMsgCount0, byzMsgCount1, numByzantine>>

\* Total messages received by process p
TotalMsgs(p) == msgCount0[p] + msgCount1[p] + byzMsgCount0[p] + byzMsgCount1[p]

\* A correct process decides after receiving N-T messages
Decide(p) ==
    /\ ~byzantine[p]
    /\ procState[p] = "proposed"
    /\ TotalMsgs(p) >= N - T
    /\ LET total0 == msgCount0[p] + byzMsgCount0[p]
           total1 == msgCount1[p] + byzMsgCount1[p]
       IN
       /\ decision' = [decision EXCEPT ![p] = 
                        IF total0 >= N - T THEN 0
                        ELSE IF total1 >= N - T THEN 1
                        ELSE IF proposal[p] = 0 THEN 0
                        ELSE IF proposal[p] = 1 THEN 1
                        ELSE "undecided"]
       /\ procState' = [procState EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<proposal, byzantine, msgCount0, msgCount1, 
                   byzMsgCount0, byzMsgCount1, proposed, numByzantine>>

\* Make a process Byzantine (can only happen if we haven't reached F Byzantine processes)
BecomeByzantine(p) ==
    /\ ~byzantine[p]
    /\ numByzantine < F
    /\ byzantine' = [byzantine EXCEPT ![p] = TRUE]
    /\ numByzantine' = numByzantine + 1
    /\ UNCHANGED <<procState, proposal, decision, msgCount0, msgCount1, 
                   byzMsgCount0, byzMsgCount1, proposed>>

\* Byzantine process sends arbitrary message (0 or 1) to all processes
ByzantineSend(p, v) ==
    /\ byzantine[p]
    /\ v \in Values
    /\ byzMsgCount0' = [q \in Procs |-> 
                          IF v = 0 
                          THEN byzMsgCount0[q] + 1 
                          ELSE byzMsgCount0[q]]
    /\ byzMsgCount1' = [q \in Procs |-> 
                          IF v = 1 
                          THEN byzMsgCount1[q] + 1 
                          ELSE byzMsgCount1[q]]
    /\ UNCHANGED <<procState, proposal, decision, byzantine, msgCount0, msgCount1, 
                   proposed, numByzantine>>

Next ==
    \/ \E p \in Procs : Propose(p)
    \/ \E p \in Procs : Decide(p)
    \/ \E p \in Procs : BecomeByzantine(p)
    \/ \E p \in Procs, v \in Values : ByzantineSend(p, v)

\* Fairness: correct processes eventually propose and decide
Fairness ==
    /\ \A p \in Procs : WF_vars(Propose(p))
    /\ \A p \in Procs : WF_vars(Decide(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* All correct processes initially propose 0
AllCorrectPropose0 ==
    \A p \in Procs : ~byzantine[p] => proposal[p] = 0

\* All correct processes initially propose 1
AllCorrectPropose1 ==
    \A p \in Procs : ~byzantine[p] => proposal[p] = 1

\* Safety Property 1: If all correct processes initially propose 0, 
\* no correct process ever decides 1 or enters undecided state
Safety1 ==
    AllCorrectPropose0 => 
        \A p \in Procs : ~byzantine[p] => 
            (decision[p] # 1 /\ decision[p] # "undecided")

\* Safety Property 2a: If all correct processes initially propose 1,
\* no correct process enters undecided state
Safety2a ==
    AllCorrectPropose1 =>
        \A p \in Procs : ~byzantine[p] => decision[p] # "undecided"

\* Safety Property 2b (Liveness): If all correct processes initially propose 1,
\* they all eventually decide 1
Liveness2 ==
    AllCorrectPropose1 ~>
        (\A p \in Procs : ~byzantine[p] => decision[p] = 1)

\* Safety Property 3 (Liveness): Under all-ones initialization, 
\* every correct process eventually decides 1
Liveness3 ==
    AllCorrectPropose1 ~>
        (\A p \in Procs : ~byzantine[p] => 
            (procState[p] = "decided" /\ decision[p] = 1))

\* Combined type safety invariant
TypeSafety ==
    /\ TypeOK
    /\ numByzantine <= F
    /\ \A p \in Procs : msgCount0[p] + msgCount1[p] <= N
    /\ \A p \in Procs : byzMsgCount0[p] + byzMsgCount1[p] <= N

\* Agreement: No two correct processes decide differently (except "none" which means not yet decided)
Agreement ==
    \A p, q \in Procs :
        (/\ ~byzantine[p] 
         /\ ~byzantine[q]
         /\ decision[p] \in Values 
         /\ decision[q] \in Values)
        => decision[p] = decision[q]

\* Validity: If a correct process decides v, then v was proposed by some correct process
Validity ==
    \A p \in Procs :
        (~byzantine[p] /\ decision[p] \in Values) =>
            \E q \in Procs : ~byzantine[q] /\ proposal[q] = decision[p]

===================================================================================