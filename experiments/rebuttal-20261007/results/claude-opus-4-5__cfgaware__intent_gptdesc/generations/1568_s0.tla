---------------------------- MODULE Bakery ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumProcs, MaxTicket

ASSUME NumProcs \in Nat /\ NumProcs > 0
ASSUME MaxTicket \in Nat /\ MaxTicket > 0

Procs == 1..NumProcs

VARIABLES
    pc,         \* Program counter for each thread
    choosing,   \* choosing[i] = TRUE when thread i is choosing a ticket
    ticket,     \* ticket[i] = ticket number for thread i (0 means not in contention)
    j           \* j[i] = index of thread that i is currently checking in wait loop

vars == <<pc, choosing, ticket, j>>

\* Program counter states
\* "idle"     - not trying to enter CS
\* "choose"   - about to start choosing
\* "choosing" - in the process of choosing (computing max)
\* "wait"     - waiting to enter CS
\* "check"    - checking if thread j has priority
\* "cs"       - in critical section
\* "exit"     - exiting critical section

TypeOK ==
    /\ pc \in [Procs -> {"idle", "choose", "choosing", "wait", "check", "cs", "exit"}]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ ticket \in [Procs -> 0..MaxTicket]
    /\ j \in [Procs -> Procs]

Init ==
    /\ pc = [i \in Procs |-> "idle"]
    /\ choosing = [i \in Procs |-> FALSE]
    /\ ticket = [i \in Procs |-> 0]
    /\ j = [i \in Procs |-> 1]

\* Thread i decides to try entering critical section
TryEnter(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "choose"]
    /\ UNCHANGED <<choosing, ticket, j>>

\* Thread i starts choosing - sets choosing flag
StartChoosing(i) ==
    /\ pc[i] = "choose"
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "choosing"]
    /\ UNCHANGED <<ticket, j>>

\* Thread i picks a ticket number (max of all tickets + 1)
PickTicket(i) ==
    /\ pc[i] = "choosing"
    /\ LET maxTicket == IF Procs = {} THEN 0
                        ELSE LET S == {ticket[k] : k \in Procs}
                             IN CHOOSE m \in S : \A n \in S : n <= m
           newTicket == maxTicket + 1
       IN /\ newTicket <= MaxTicket  \* Guard to ensure boundedness
          /\ ticket' = [ticket EXCEPT ![i] = newTicket]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ j' = [j EXCEPT ![i] = 1]  \* Start checking from thread 1
    /\ pc' = [pc EXCEPT ![i] = "wait"]

\* Thread i starts checking thread j[i]
StartWait(i) ==
    /\ pc[i] = "wait"
    /\ j[i] <= NumProcs
    /\ pc' = [pc EXCEPT ![i] = "check"]
    /\ UNCHANGED <<choosing, ticket, j>>

\* Thread i checks if it can pass thread j[i]
\* Must wait if j[i] is choosing or has priority
CheckThread(i) ==
    /\ pc[i] = "check"
    /\ j[i] <= NumProcs
    /\ choosing[j[i]] = FALSE  \* Wait until j[i] is not choosing
    /\ \/ ticket[j[i]] = 0     \* j[i] not competing
       \/ ticket[j[i]] > ticket[i]  \* i has smaller ticket (higher priority)
       \/ /\ ticket[j[i]] = ticket[i]  \* Same ticket, use thread id as tiebreaker
          /\ j[i] > i
    /\ j' = [j EXCEPT ![i] = j[i] + 1]  \* Move to next thread
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED <<choosing, ticket>>

\* Thread i has checked all threads and can enter CS
EnterCS(i) ==
    /\ pc[i] = "wait"
    /\ j[i] > NumProcs  \* Checked all threads
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<choosing, ticket, j>>

\* Thread i exits critical section
ExitCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<choosing, ticket, j>>

\* Thread i releases ticket and returns to idle
Release(i) ==
    /\ pc[i] = "exit"
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED <<choosing, j>>

\* All actions for thread i
Thread(i) ==
    \/ TryEnter(i)
    \/ StartChoosing(i)
    \/ PickTicket(i)
    \/ StartWait(i)
    \/ CheckThread(i)
    \/ EnterCS(i)
    \/ ExitCS(i)
    \/ Release(i)

Next == \E i \in Procs : Thread(i)

\* Fairness: weak fairness for each thread's actions
\* This ensures that if a thread can continuously make progress, it eventually will
Fairness == \A i \in Procs : WF_vars(Thread(i))

\* The complete specification
Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* SAFETY PROPERTIES

\* Mutual Exclusion: at most one thread in critical section
MutualExclusion ==
    \A i, k \in Procs : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

\* Boundedness: all tickets are within bounds
TicketBoundedness ==
    \A i \in Procs : ticket[i] <= MaxTicket

\* The main invariant combining all safety properties
Invariant == TypeOK /\ MutualExclusion /\ TicketBoundedness

-----------------------------------------------------------------------------
\* LIVENESS PROPERTIES

\* Starvation Freedom: if a thread starts trying, it eventually enters CS
\* (requires fairness assumption)
StarvationFreedom ==
    \A i \in Procs : (pc[i] = "choose") ~> (pc[i] = "cs")

\* Progress: if some thread is trying, eventually some thread enters CS
Progress ==
    (\E i \in Procs : pc[i] \in {"choose", "choosing", "wait", "check"}) 
    ~> (\E i \in Procs : pc[i] = "cs")

\* Deadlock Freedom: it's always possible to make progress
\* (either some thread is in CS, or some thread can take a step)
DeadlockFreedom ==
    [](\E i \in Procs : pc[i] # "idle" => 
       \/ pc[i] = "cs"
       \/ ENABLED(Thread(i)))

\* Liveness property combining starvation freedom
Liveness == \A i \in Procs : [](pc[i] = "choose" => <>(pc[i] = "cs"))

=============================================================================