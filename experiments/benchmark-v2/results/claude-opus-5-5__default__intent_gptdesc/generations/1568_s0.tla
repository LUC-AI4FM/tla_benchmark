------------------------------- MODULE Bakery -------------------------------
(***************************************************************************)
(* Lamport's Bakery mutual-exclusion algorithm for N threads.              *)
(*                                                                         *)
(* Each thread i in Procs = 1..N runs this loop:                           *)
(*                                                                         *)
(*   ncs : non-critical section                                            *)
(*   e1  : choosing[i] := TRUE ; mx := 0 ; unread := Procs \ {i}           *)
(*   e2  : while unread # {} : read num[j] for some j in unread            *)
(*                             mx := max(mx, num[j])                       *)
(*   e3  : num[i] := mx + 1    (abort to "gate" if mx+1 > MaxTicket)       *)
(*   e4  : choosing[i] := FALSE ; unread := Procs \ {i}                    *)
(*   w1  : while unread # {} : pick nxt in unread                          *)
(*   w2  :     await ~choosing[nxt]                                        *)
(*   w3  :     await num[nxt] = 0 \/ <<num[i],i>> << <<num[nxt],nxt>>      *)
(*             unread := unread \ {nxt}                                    *)
(*   cs  : critical section                                                *)
(*   exit: num[i] := 0 ; goto ncs                                          *)
(*                                                                         *)
(* Reads and writes of shared variables are separate atomic steps, so any  *)
(* interleaving of threads is possible.                                    *)
(*                                                                         *)
(* Bounding tickets for model checking: if the ticket a thread would take  *)
(* is larger than MaxTicket, it does not take it. Instead it clears its    *)
(* choosing flag (its ticket is still 0) and waits at "gate". It leaves    *)
(* the gate only when every ticket is 0, and then restarts its doorway.    *)
(* This is a modelling device, not part of the original algorithm.         *)
(*                                                                         *)
(* The gate keeps every ticket within 0..MaxTicket by construction. It     *)
(* does not affect mutual exclusion: a waiting thread holds no ticket and  *)
(* is not choosing, so it never blocks anyone.                             *)
(*                                                                         *)
(* Why MaxTicket >= N matters: when a thread leaves the gate, every ticket *)
(* is 0. Until it finishes choosing, each other thread can take at most    *)
(* one ticket, because that thread's next pass through w2 blocks on this   *)
(* thread's choosing flag. So those tickets are at most N-1, and the       *)
(* thread's own ticket is at most N.                                       *)
(*                                                                         *)
(* Fairness:                                                               *)
(* - Every thread is weakly fair for all its ordinary steps. A thread that *)
(*   stays continuously able to move eventually moves.                     *)
(* - Every thread is strongly fair for the gate step. Its condition (all   *)
(*   tickets 0) may hold only some of the time; strong fairness means a    *)
(*   thread for which it holds infinitely often eventually passes.         *)
(* - Threads always leave the non-critical section again, so every thread  *)
(*   tries to enter the critical section over and over.                    *)
(*                                                                         *)
(* Starvation-freedom is claimed only under these assumptions. The gate is *)
(* a modelling device, so treat the liveness properties as properties to  *)
(* check with TLC for the chosen N and MaxTicket.                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,          \* number of threads
    MaxTicket   \* upper bound on ticket values (for model checking)

ASSUME NAssump   == N \in Nat \ {0}
ASSUME MaxAssump == MaxTicket \in Nat /\ MaxTicket >= N

Procs == 1..N

VARIABLES
    num,        \* num[i]      : ticket of thread i (0 = no ticket)
    choosing,   \* choosing[i] : TRUE while thread i is in its doorway
    pc,         \* pc[i]       : control location of thread i
    unread,     \* unread[i]   : peers thread i still has to read or check
    mx,         \* mx[i]       : largest ticket thread i has seen so far
    nxt         \* nxt[i]      : peer thread i is checking in its wait loop

vars == << num, choosing, pc, unread, mx, nxt >>

Labels == {"ncs", "e1", "e2", "e3", "e4", "gate",
           "w1", "w2", "w3", "cs", "exit"}

\* Locations where a thread is trying to enter the critical section
Trying == {"e1", "e2", "e3", "e4", "gate", "w1", "w2", "w3"}

\* Lexicographic priority: thread i comes before thread j
Before(i, j) ==
    \/ num[i] < num[j]
    \/ /\ num[i] = num[j]
       /\ i < j

-----------------------------------------------------------------------------
TypeOK ==
    /\ num      \in [Procs -> 0..MaxTicket]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ pc       \in [Procs -> Labels]
    /\ unread   \in [Procs -> SUBSET Procs]
    /\ mx       \in [Procs -> 0..MaxTicket]
    /\ nxt      \in [Procs -> Procs]

Init ==
    /\ num      = [i \in Procs |-> 0]
    /\ choosing = [i \in Procs |-> FALSE]
    /\ pc       = [i \in Procs |-> "ncs"]
    /\ unread   = [i \in Procs |-> {}]
    /\ mx       = [i \in Procs |-> 0]
    /\ nxt      = [i \in Procs |-> i]

-----------------------------------------------------------------------------
(* Thread actions *)

\* Leave the non-critical section
Ncs(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "e1"]
    /\ UNCHANGED << num, choosing, unread, mx, nxt >>

\* Start the doorway: set choosing, prepare to read peers' tickets
E1(i) ==
    /\ pc[i] = "e1"
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ unread'   = [unread EXCEPT ![i] = Procs \ {i}]
    /\ mx'       = [mx EXCEPT ![i] = 0]
    /\ pc'       = [pc EXCEPT ![i] = "e2"]
    /\ UNCHANGED << num, nxt >>

\* Read one peer's ticket (in any order), or finish reading
E2(i) ==
    /\ pc[i] = "e2"
    /\ IF unread[i] # {}
          THEN \E j \in unread[i] :
                 /\ mx' = [mx EXCEPT ![i] =
                              IF num[j] > mx[i] THEN num[j] ELSE mx[i]]
                 /\ unread' = [unread EXCEPT ![i] = unread[i] \ {j}]
                 /\ UNCHANGED pc
          ELSE /\ pc' = [pc EXCEPT ![i] = "e3"]
               /\ UNCHANGED << mx, unread >>
    /\ UNCHANGED << num, choosing, nxt >>

\* Take ticket mx+1, or abort to the gate if it would exceed MaxTicket
E3(i) ==
    /\ pc[i] = "e3"
    /\ IF mx[i] + 1 <= MaxTicket
          THEN /\ num' = [num EXCEPT ![i] = mx[i] + 1]
               /\ pc'  = [pc EXCEPT ![i] = "e4"]
               /\ UNCHANGED choosing
          ELSE /\ choosing' = [choosing EXCEPT ![i] = FALSE]
               /\ pc'       = [pc EXCEPT ![i] = "gate"]
               /\ UNCHANGED num
    /\ UNCHANGED << unread, mx, nxt >>

\* Finish choosing and prepare the wait loop
E4(i) ==
    /\ pc[i] = "e4"
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ unread'   = [unread EXCEPT ![i] = Procs \ {i}]
    /\ pc'       = [pc EXCEPT ![i] = "w1"]
    /\ UNCHANGED << num, mx, nxt >>

\* Bounding device: restart the doorway once every ticket is 0
Gate(i) ==
    /\ pc[i] = "gate"
    /\ \A j \in Procs : num[j] = 0
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ unread'   = [unread EXCEPT ![i] = Procs \ {i}]
    /\ mx'       = [mx EXCEPT ![i] = 0]
    /\ pc'       = [pc EXCEPT ![i] = "e2"]
    /\ UNCHANGED << num, nxt >>

\* Wait loop: pick the next peer to check, or enter the CS when done
W1(i) ==
    /\ pc[i] = "w1"
    /\ IF unread[i] # {}
          THEN \E j \in unread[i] :
                 /\ nxt' = [nxt EXCEPT ![i] = j]
                 /\ pc'  = [pc EXCEPT ![i] = "w2"]
          ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
               /\ UNCHANGED nxt
    /\ UNCHANGED << num, choosing, unread, mx >>

\* Wait until the peer is not choosing
W2(i) ==
    /\ pc[i] = "w2"
    /\ ~choosing[nxt[i]]
    /\ pc' = [pc EXCEPT ![i] = "w3"]
    /\ UNCHANGED << num, choosing, unread, mx, nxt >>

\* Wait until the peer has no ticket or has lower priority
W3(i) ==
    /\ pc[i] = "w3"
    /\ \/ num[nxt[i]] = 0
       \/ Before(i, nxt[i])
    /\ unread' = [unread EXCEPT ![i] = unread[i] \ {nxt[i]}]
    /\ pc'     = [pc EXCEPT ![i] = "w1"]
    /\ UNCHANGED << num, choosing, mx, nxt >>

\* Critical section
CS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED << num, choosing, unread, mx, nxt >>

\* Exit: release the ticket and go back to the non-critical section
Exit(i) ==
    /\ pc[i] = "exit"
    /\ num' = [num EXCEPT ![i] = 0]
    /\ pc'  = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED << choosing, unread, mx, nxt >>

\* All of thread i's steps except the gate
Ordinary(i) ==
    \/ Ncs(i) \/ E1(i) \/ E2(i) \/ E3(i) \/ E4(i)
    \/ W1(i)  \/ W2(i) \/ W3(i) \/ CS(i) \/ Exit(i)

Proc(i) == Ordinary(i) \/ Gate(i)

\* Any thread that can move may take the next step
Next == \E i \in Procs : Proc(i)

-----------------------------------------------------------------------------
(* Fairness assumption *)

Fairness ==
    \A i \in Procs :
        /\ WF_vars(Ordinary(i))
        /\ SF_vars(Gate(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties (invariants) *)

\* At most one thread is in the critical section
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Ticket values stay within the declared bound
TicketBound ==
    \A i \in Procs : num[i] \in 0..MaxTicket

\* No deadlock: if some thread is trying to enter or is inside the
\* critical section, some thread can take a step
DeadlockFree ==
    (\E i \in Procs : pc[i] \in Trying \cup {"cs", "exit"})
        => ENABLED Next

\* No thread is ever permanently disabled with nothing able to move
NoGlobalStall == ENABLED Next

Safety == TypeOK /\ MutualExclusion /\ TicketBound /\ DeadlockFree

-----------------------------------------------------------------------------
(* Liveness properties (checked under Fairness) *)

\* Starvation-freedom: every thread that tries eventually enters the CS
StarvationFree ==
    \A i \in Procs : (pc[i] \in Trying) ~> (pc[i] = "cs")

\* Each thread enters the critical section infinitely often
InfinitelyOftenCS ==
    \A i \in Procs : []<>(pc[i] = "cs")

\* Global progress: if some thread is trying, some thread gets in
Progress ==
    (\E i \in Procs : pc[i] \in Trying) ~> (\E i \in Procs : pc[i] = "cs")

-----------------------------------------------------------------------------
THEOREM SafetyThm   == Spec => [](TypeOK /\ MutualExclusion /\ TicketBound /\ DeadlockFree)
THEOREM LivenessThm == Spec => (StarvationFree /\ Progress /\ InfinitelyOftenCS)

=============================================================================