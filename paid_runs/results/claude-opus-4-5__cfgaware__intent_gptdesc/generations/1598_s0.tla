---------------------------- MODULE FastMutex ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES
    intent,      \* intent[i] = TRUE means process i wants to enter CS
    tour1,       \* First coordination register (process id or 0)
    tour2,       \* Second coordination register (process id or 0)
    pc           \* Program counter for each process

vars == <<intent, tour1, tour2, pc>>

Procs == 1..N

\* Program counter states:
\* "idle"      - not trying to enter
\* "set_intent" - about to set intent flag
\* "write_tour1" - write to first tour variable
\* "read_tour1"  - read tour1 to check if we're first
\* "write_tour2" - write to second tour variable  
\* "check_tour2" - check second tour variable
\* "spin_intent" - spinning waiting for other intents to clear
\* "check_tour1_final" - final check of tour1
\* "cs"        - in critical section
\* "exit"      - exiting, cleanup

PCStates == {"idle", "set_intent", "write_tour1", "read_tour1", 
             "write_tour2", "check_tour2", "spin_intent", 
             "check_tour1_final", "cs", "exit"}

TypeOK ==
    /\ intent \in [Procs -> BOOLEAN]
    /\ tour1 \in 0..N
    /\ tour2 \in 0..N
    /\ pc \in [Procs -> PCStates]

Init ==
    /\ intent = [i \in Procs |-> FALSE]
    /\ tour1 = 0
    /\ tour2 = 0
    /\ pc = [i \in Procs |-> "idle"]

\* Process i starts attempting to enter critical section
StartEntry(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "set_intent"]
    /\ UNCHANGED <<intent, tour1, tour2>>

\* Process i sets its intent flag
SetIntent(i) ==
    /\ pc[i] = "set_intent"
    /\ intent' = [intent EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "write_tour1"]
    /\ UNCHANGED <<tour1, tour2>>

\* Process i writes to tour1
WriteTour1(i) ==
    /\ pc[i] = "write_tour1"
    /\ tour1' = i
    /\ pc' = [pc EXCEPT ![i] = "read_tour1"]
    /\ UNCHANGED <<intent, tour2>>

\* Process i reads tour1 and decides next step
ReadTour1(i) ==
    /\ pc[i] = "read_tour1"
    /\ IF tour2 /= 0
       THEN \* Someone else might be ahead, need to back off and retry
            /\ pc' = [pc EXCEPT ![i] = "check_tour2"]
            /\ UNCHANGED <<intent, tour1, tour2>>
       ELSE \* We might be first, proceed to write tour2
            /\ pc' = [pc EXCEPT ![i] = "write_tour2"]
            /\ UNCHANGED <<intent, tour1, tour2>>

\* Process i writes to tour2
WriteTour2(i) ==
    /\ pc[i] = "write_tour2"
    /\ tour2' = i
    /\ pc' = [pc EXCEPT ![i] = "check_tour1_final"]
    /\ UNCHANGED <<intent, tour1>>

\* Process i checks tour2 - if someone else, back off
CheckTour2(i) ==
    /\ pc[i] = "check_tour2"
    /\ IF tour2 = i
       THEN \* We own tour2, can proceed to final check
            /\ pc' = [pc EXCEPT ![i] = "check_tour1_final"]
            /\ UNCHANGED <<intent, tour1, tour2>>
       ELSE \* Need to wait and retry - go to spin state
            /\ pc' = [pc EXCEPT ![i] = "spin_intent"]
            /\ UNCHANGED <<intent, tour1, tour2>>

\* Process i spins waiting for other intents to clear before retrying
SpinIntent(i) ==
    /\ pc[i] = "spin_intent"
    /\ \/ /\ \A j \in Procs \ {i} : ~intent[j]  \* All others have cleared intent
          /\ pc' = [pc EXCEPT ![i] = "write_tour1"]  \* Retry from tour1 write
          /\ UNCHANGED <<intent, tour1, tour2>>
       \/ /\ \E j \in Procs \ {i} : intent[j]  \* Still someone with intent
          /\ tour2 = i  \* We now own tour2
          /\ pc' = [pc EXCEPT ![i] = "check_tour1_final"]
          /\ UNCHANGED <<intent, tour1, tour2>>
       \/ /\ \E j \in Procs \ {i} : intent[j]  \* Still someone with intent  
          /\ tour2 /= i  \* We don't own tour2, keep spinning
          /\ pc' = [pc EXCEPT ![i] = "spin_intent"]
          /\ UNCHANGED <<intent, tour1, tour2>>

\* Process i does final check of tour1
CheckTour1Final(i) ==
    /\ pc[i] = "check_tour1_final"
    /\ IF tour1 = i
       THEN \* Fast path - we're definitely first
            /\ pc' = [pc EXCEPT ![i] = "cs"]
            /\ UNCHANGED <<intent, tour1, tour2>>
       ELSE \* Slow path - need to wait for others
            /\ \A j \in Procs \ {i} : ~intent[j]  \* Wait until all others clear
            /\ IF tour2 = i
               THEN /\ pc' = [pc EXCEPT ![i] = "cs"]
                    /\ UNCHANGED <<intent, tour1, tour2>>
               ELSE \* Lost the race, back off and retry
                    /\ pc' = [pc EXCEPT ![i] = "spin_intent"]
                    /\ UNCHANGED <<intent, tour1, tour2>>

\* Process i enters critical section
EnterCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<intent, tour1, tour2>>

\* Process i exits and cleans up
Exit(i) ==
    /\ pc[i] = "exit"
    /\ intent' = [intent EXCEPT ![i] = FALSE]
    /\ tour2' = IF tour2 = i THEN 0 ELSE tour2
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED tour1

\* Abort and retry - process can give up and restart from idle
\* This models back-off behavior
Abort(i) ==
    /\ pc[i] \in {"set_intent", "write_tour1", "read_tour1", 
                  "write_tour2", "check_tour2", "spin_intent", 
                  "check_tour1_final"}
    /\ intent' = [intent EXCEPT ![i] = FALSE]
    /\ tour2' = IF tour2 = i THEN 0 ELSE tour2
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED tour1

\* All actions for process i
ProcAction(i) ==
    \/ StartEntry(i)
    \/ SetIntent(i)
    \/ WriteTour1(i)
    \/ ReadTour1(i)
    \/ WriteTour2(i)
    \/ CheckTour2(i)
    \/ SpinIntent(i)
    \/ CheckTour1Final(i)
    \/ EnterCS(i)
    \/ Exit(i)
    \/ Abort(i)

Next == \E i \in Procs : ProcAction(i)

\* Fairness: weak fairness on each process's actions
Fairness == \A i \in Procs : WF_vars(ProcAction(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual exclusion - at most one process in CS
MutualExclusion ==
    \A i, j \in Procs : (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Alternative formulation
AtMostOneInCS ==
    Cardinality({i \in Procs : pc[i] = "cs"}) <= 1

Invariant == MutualExclusion /\ TypeOK

\* Liveness: If processes keep trying, eventually some process enters CS
\* System-wide starvation freedom
SomeoneEntersCS == \E i \in Procs : pc[i] = "cs"
SomeoneTrying == \E i \in Procs : pc[i] /= "idle"

\* Infinitely often some process enters CS (if someone is trying)
SystemProgress == []<>SomeoneEntersCS

\* Per-process eventual entry under weak fairness
ProcessEventualEntry(i) == (pc[i] = "set_intent") ~> (pc[i] = "cs")
AllProcessesEventualEntry == \A i \in Procs : ProcessEventualEntry(i)

\* Combined liveness property
Liveness == SystemProgress /\ AllProcessesEventualEntry

==========================================================================