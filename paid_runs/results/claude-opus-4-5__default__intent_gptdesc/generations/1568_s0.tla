-------------------------------- MODULE Bakery --------------------------------
\* Lamport's Bakery Algorithm for Mutual Exclusion
\* Models N concurrent threads competing for a single critical section

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS 
    Threads,        \* Set of thread identifiers
    MaxTicket       \* Upper bound on ticket values for model checking

ASSUME Threads # {}
ASSUME MaxTicket \in Nat /\ MaxTicket >= Cardinality(Threads)

VARIABLES
    pc,             \* Program counter for each thread
    choosing,       \* choosing[t] = TRUE when thread t is selecting a ticket
    ticket,         \* ticket[t] = ticket number of thread t (0 means not waiting)
    maxSeen,        \* maxSeen[t] = maximum ticket observed during choosing phase
    checkingThread  \* checkingThread[t] = which thread t is currently checking in wait phase

vars == <<pc, choosing, ticket, maxSeen, checkingThread>>

\* Program counter states
States == {"idle", "startChoosing", "readTickets", "endChoosing", 
           "waitLoop", "checkChoosing", "checkTicket", "cs", "exit"}

\* Thread t has priority over thread s in the waiting protocol
\* Returns TRUE if t should wait for s
HasPriority(s, t) ==
    /\ ticket[s] # 0
    /\ \/ ticket[s] < ticket[t]
       \/ (ticket[s] = ticket[t] /\ s < t)

TypeOK ==
    /\ pc \in [Threads -> States]
    /\ choosing \in [Threads -> BOOLEAN]
    /\ ticket \in [Threads -> 0..MaxTicket]
    /\ maxSeen \in [Threads -> 0..MaxTicket]
    /\ checkingThread \in [Threads -> Threads]

Init ==
    /\ pc = [t \in Threads |-> "idle"]
    /\ choosing = [t \in Threads |-> FALSE]
    /\ ticket = [t \in Threads |-> 0]
    /\ maxSeen = [t \in Threads |-> 0]
    /\ checkingThread = [t \in Threads |-> CHOOSE x \in Threads : TRUE]

\* Thread t starts the protocol - sets choosing flag
StartChoosing(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "startChoosing"]
    /\ choosing' = [choosing EXCEPT ![t] = TRUE]
    /\ maxSeen' = [maxSeen EXCEPT ![t] = 0]
    /\ UNCHANGED <<ticket, checkingThread>>

\* Thread t reads all tickets and computes maximum
ReadTickets(t) ==
    /\ pc[t] = "startChoosing"
    /\ LET maxTicketValue == IF Threads = {} THEN 0
                            ELSE LET ticketSet == {ticket[s] : s \in Threads}
                                 IN CHOOSE m \in ticketSet : \A n \in ticketSet : n <= m
       IN maxSeen' = [maxSeen EXCEPT ![t] = maxTicketValue]
    /\ pc' = [pc EXCEPT ![t] = "readTickets"]
    /\ UNCHANGED <<choosing, ticket, checkingThread>>

\* Thread t finishes choosing - takes ticket and clears choosing flag
EndChoosing(t) ==
    /\ pc[t] = "readTickets"
    /\ maxSeen[t] + 1 <= MaxTicket  \* Ensure we don't exceed bound
    /\ ticket' = [ticket EXCEPT ![t] = maxSeen[t] + 1]
    /\ choosing' = [choosing EXCEPT ![t] = FALSE]
    /\ pc' = [pc EXCEPT ![t] = "endChoosing"]
    /\ UNCHANGED <<maxSeen, checkingThread>>

\* Thread t initializes the wait loop - picks first thread to check
StartWaitLoop(t) ==
    /\ pc[t] = "endChoosing"
    /\ checkingThread' = [checkingThread EXCEPT ![t] = CHOOSE x \in Threads : TRUE]
    /\ pc' = [pc EXCEPT ![t] = "waitLoop"]
    /\ UNCHANGED <<choosing, ticket, maxSeen>>

\* Thread t checks if thread s is choosing
CheckChoosing(t) ==
    /\ pc[t] = "waitLoop"
    /\ LET s == checkingThread[t]
       IN IF choosing[s]
          THEN /\ pc' = [pc EXCEPT ![t] = "checkChoosing"]  \* Wait and retry
               /\ UNCHANGED <<choosing, ticket, maxSeen, checkingThread>>
          ELSE /\ pc' = [pc EXCEPT ![t] = "checkTicket"]
               /\ UNCHANGED <<choosing, ticket, maxSeen, checkingThread>>

\* Thread t waits while thread s is choosing (stays in checkChoosing until s done)
WaitForChoosing(t) ==
    /\ pc[t] = "checkChoosing"
    /\ LET s == checkingThread[t]
       IN IF ~choosing[s]
          THEN pc' = [pc EXCEPT ![t] = "checkTicket"]
          ELSE pc' = [pc EXCEPT ![t] = "checkChoosing"]  \* Keep waiting
    /\ UNCHANGED <<choosing, ticket, maxSeen, checkingThread>>

\* Thread t checks ticket priority against thread s
CheckTicketPriority(t) ==
    /\ pc[t] = "checkTicket"
    /\ LET s == checkingThread[t]
       IN IF HasPriority(s, t)
          THEN \* Must wait for s - stay in checkTicket
               /\ pc' = [pc EXCEPT ![t] = "checkTicket"]
               /\ UNCHANGED <<choosing, ticket, maxSeen, checkingThread>>
          ELSE \* s doesn't have priority, move to next thread or enter CS
               /\ LET nextThreads == {x \in Threads : x # s /\ 
                                      \A y \in Threads : (y # s /\ checkingThread[t] = s) => 
                                                         (x >= checkingThread[t] \/ x < s)}
                      allChecked == \A x \in Threads : 
                                    x = s \/ 
                                    (ticket[x] = 0 \/ 
                                     ticket[t] < ticket[x] \/ 
                                     (ticket[t] = ticket[x] /\ t < x))
                  IN IF allChecked /\ ~HasPriority(s, t)
                     THEN \* Check if we've verified all threads
                          LET remaining == {x \in Threads : x # t /\ 
                                           (choosing[x] \/ HasPriority(x, t))}
                          IN IF remaining = {}
                             THEN pc' = [pc EXCEPT ![t] = "cs"]
                             ELSE \* Move to next thread to check
                                  LET nextT == CHOOSE x \in Threads : TRUE
                                  IN /\ checkingThread' = [checkingThread EXCEPT ![t] = nextT]
                                     /\ pc' = [pc EXCEPT ![t] = "waitLoop"]
                     ELSE /\ pc' = [pc EXCEPT ![t] = "checkTicket"]
                          /\ UNCHANGED checkingThread
               /\ UNCHANGED <<choosing, ticket, maxSeen>>

\* Simplified: Thread t advances to next thread in wait loop or enters CS
AdvanceWait(t) ==
    /\ pc[t] = "checkTicket"
    /\ LET s == checkingThread[t]
       IN /\ ~HasPriority(s, t)  \* s doesn't block t
          /\ LET otherThreads == Threads \ {s}
                 uncheckedWithPriority == {x \in otherThreads : choosing[x] \/ HasPriority(x, t)}
             IN IF uncheckedWithPriority = {}
                THEN \* All threads checked, can enter CS
                     /\ pc' = [pc EXCEPT ![t] = "cs"]
                     /\ UNCHANGED checkingThread
                ELSE \* Move to check another thread
                     /\ checkingThread' = [checkingThread EXCEPT ![t] = 
                                          CHOOSE x \in Threads : x # s]
                     /\ pc' = [pc EXCEPT ![t] = "waitLoop"]
    /\ UNCHANGED <<choosing, ticket, maxSeen>>

\* More accurate wait implementation: thread t is in the wait phase
Wait(t) ==
    /\ pc[t] \in {"waitLoop", "checkChoosing", "checkTicket"}
    /\ LET canEnter == \A s \in Threads \ {t} :
                       /\ ~choosing[s]
                       /\ ~HasPriority(s, t)
       IN IF canEnter
          THEN /\ pc' = [pc EXCEPT ![t] = "cs"]
               /\ UNCHANGED <<choosing, ticket, maxSeen, checkingThread>>
          ELSE /\ pc' = pc  \* Stay waiting
               /\ UNCHANGED <<choosing, ticket, maxSeen, checkingThread>>

\* Thread t is in the critical section
InCS(t) ==
    /\ pc[t] = "cs"
    /\ pc' = [pc EXCEPT ![t] = "exit"]
    /\ UNCHANGED <<choosing, ticket, maxSeen, checkingThread>>

\* Thread t exits the critical section
Exit(t) ==
    /\ pc[t] = "exit"
    /\ ticket' = [ticket EXCEPT ![t] = 0]
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<choosing, maxSeen, checkingThread>>

\* Combined Next for a cleaner specification
ThreadStep(t) ==
    \/ StartChoosing(t)
    \/ ReadTickets(t)
    \/ EndChoosing(t)
    \/ StartWaitLoop(t)
    \/ CheckChoosing(t)
    \/ WaitForChoosing(t)
    \/ /\ pc[t] \in {"waitLoop", "checkChoosing", "checkTicket"}
       /\ LET canEnter == \A s \in Threads \ {t} :
                          /\ ~choosing[s]
                          /\ ~HasPriority(s, t)
          IN /\ canEnter
             /\ pc' = [pc EXCEPT ![t] = "cs"]
             /\ UNCHANGED <<choosing, ticket, maxSeen, checkingThread>>
    \/ /\ pc[t] \in {"waitLoop", "checkChoosing", "checkTicket"}
       /\ LET canEnter == \A s \in Threads \ {t} :
                          /\ ~choosing[s]
                          /\ ~HasPriority(s, t)
          IN /\ ~canEnter
             /\ pc' = pc
             /\ UNCHANGED <<choosing, ticket, maxSeen, checkingThread>>
    \/ InCS(t)
    \/ Exit(t)

Next == \E t \in Threads : ThreadStep(t)

\* Fairness: weak fairness for each thread's actions
Fairness == \A t \in Threads : WF_vars(ThreadStep(t))

Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
\* SAFETY PROPERTIES
--------------------------------------------------------------------------------

\* Mutual Exclusion: at most one thread in the critical section
MutualExclusion ==
    \A t1, t2 \in Threads :
        (pc[t1] = "cs" /\ pc[t2] = "cs") => t1 = t2

\* Alternative formulation: cardinality of threads in CS is at most 1
MutualExclusionAlt ==
    Cardinality({t \in Threads : pc[t] = "cs"}) <= 1

\* Boundedness: all ticket values within bounds
TicketBoundedness ==
    \A t \in Threads : ticket[t] <= MaxTicket

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ MutualExclusion
    /\ TicketBoundedness

--------------------------------------------------------------------------------
\* LIVENESS PROPERTIES
--------------------------------------------------------------------------------

\* A thread trying to enter will eventually enter (starvation-freedom)
\* A thread is "trying" if it's past idle and not yet in CS
Trying(t) == pc[t] \in {"startChoosing", "readTickets", "endChoosing", 
                        "waitLoop", "checkChoosing", "checkTicket"}

\* Starvation Freedom: if a thread is trying, it will eventually enter CS
StarvationFreedom == 
    \A t \in Threads : Trying(t) ~> pc[t] = "cs"

\* Progress: if any thread is trying, eventually some thread enters CS
Progress ==
    (\E t \in Threads : Trying(t)) ~> (\E t \in Threads : pc[t] = "cs")

\* Every thread that starts choosing eventually enters CS
EventualEntry ==
    \A t \in Threads : (pc[t] = "startChoosing") ~> (pc[t] = "cs")

--------------------------------------------------------------------------------
\* DEADLOCK FREEDOM
--------------------------------------------------------------------------------

\* At least one thread can make progress when some thread is trying
SomeThreadCanProgress ==
    (\E t \in Threads : Trying(t)) => 
    (\E t \in Threads : ENABLED(ThreadStep(t)))

\* The system is not deadlocked: either no one is trying, or someone can move
DeadlockFreedom ==
    (\A t \in Threads : pc[t] = "idle") \/ 
    (\E t \in Threads : ENABLED(ThreadStep(t)))

--------------------------------------------------------------------------------
\* THEOREMS (for documentation - these are the properties to verify)
--------------------------------------------------------------------------------

\* The specification should satisfy these properties:
THEOREM Spec => []MutualExclusion
THEOREM Spec => []TicketBoundedness  
THEOREM Spec => []TypeOK
THEOREM Spec => StarvationFreedom
THEOREM Spec => Progress

================================================================================