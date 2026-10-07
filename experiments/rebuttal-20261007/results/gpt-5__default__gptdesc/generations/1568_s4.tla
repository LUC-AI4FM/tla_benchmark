----------------------------- MODULE Bakery -----------------------------
EXTENDS Naturals

CONSTANTS
    N,          \* Number of processes (N >= 1)
    MaxTicket   \* Maximum ticket value used to bound tickets for TLC

ASSUME N \in Nat \ {0} /\ MaxTicket \in Nat

Proc == 1..N

VARIABLES
    pc,         \* program counter: per-process control state
    choosing,   \* per-process flag: TRUE while choosing a ticket
    number,     \* per-process ticket number (0 means not competing)
    j           \* per-process loop index for waiting over other processes

vars == << pc, choosing, number, j >>

(*
  The usual Bakery algorithm:
    choosing[i] := TRUE;
    number[i] := 1 + Max({number[k] : k \in Proc});
    choosing[i] := FALSE;
    for j \in Proc \ {i} do
      await ~choosing[j];
      await number[j] = 0 \/ (number[j], j) > (number[i], i)
    end;
    CS;
    number[i] := 0;
*)

MaxNum ==
    CHOOSE mx \in { number[k] : k \in Proc } :
        \A n \in { number[k] : k \in Proc } : n <= mx

TypeOK ==
    /\ pc \in [Proc -> {"try1", "choose2", "choose3", "wait", "cs"}]
    /\ choosing \in [Proc -> BOOLEAN]
    /\ number \in [Proc -> Nat]
    /\ j \in [Proc -> 1..(N+1)]

TicketBound ==
    \A i \in Proc : number[i] <= MaxTicket

Mutex ==
    \A i, k \in Proc : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

Init ==
    /\ TypeOK
    /\ \A i \in Proc :
        /\ pc[i] = "try1"
        /\ choosing[i] = FALSE
        /\ number[i] = 0
        /\ j[i] = 1
    /\ TicketBound

\* Lexicographic permission condition used in waiting:
CanAdvance(i, jj) ==
    (jj = i)
    \/ (~choosing[jj]
        /\ ( number[jj] = 0
             \/ number[jj] > number[i]
             \/ (number[jj] = number[i] /\ jj > i) ))

Proc(i) ==
    \/ /\ pc[i] = "try1"
       /\ choosing' = [choosing EXCEPT ![i] = TRUE]
       /\ pc' = [pc EXCEPT ![i] = "choose2"]
       /\ UNCHANGED << number, j >>

    \/ /\ pc[i] = "choose2"
       /\ number' = [number EXCEPT ![i] = MaxNum + 1]
       /\ pc' = [pc EXCEPT ![i] = "choose3"]
       /\ UNCHANGED << choosing, j >>

    \/ /\ pc[i] = "choose3"
       /\ choosing' = [choosing EXCEPT ![i] = FALSE]
       /\ j' = [j EXCEPT ![i] = 1]
       /\ pc' = [pc EXCEPT ![i] = "wait"]
       /\ UNCHANGED number

    \* Advance the waiting loop index when allowed (skip over self)
    \/ /\ pc[i] = "wait"
       /\ j[i] <= N
       /\ j[i] = i
       /\ j' = [j EXCEPT ![i] = j[i] + 1]
       /\ pc' = pc
       /\ UNCHANGED << choosing, number >>

    \* Advance the waiting loop index when other process jj permits us
    \/ /\ pc[i] = "wait"
       /\ j[i] <= N
       /\ j[i] # i
       /\ ~choosing[j[i]]
       /\ ( number[j[i]] = 0
            \/ number[j[i]] > number[i]
            \/ (number[j[i]] = number[i] /\ j[i] > i) )
       /\ j' = [j EXCEPT ![i] = j[i] + 1]
       /\ pc' = pc
       /\ UNCHANGED << choosing, number >>

    \* Enter the critical section when all others have been checked
    \/ /\ pc[i] = "wait"
       /\ j[i] > N
       /\ pc' = [pc EXCEPT ![i] = "cs"]
       /\ UNCHANGED << choosing, number, j >>

    \* Exit the critical section, reset the ticket, and try again
    \/ /\ pc[i] = "cs"
       /\ number' = [number EXCEPT ![i] = 0]
       /\ pc' = [pc EXCEPT ![i] = "try1"]
       /\ UNCHANGED << choosing, j >>

Next ==
    \E i \in Proc : Proc(i)

\* For TLC model checking, we constrain next states to respect the ticket bound.
NextB ==
    Next /\ TicketBound'

\* Fairness per process (as in PlusCal fair process translation), w.r.t. bounded Next
ProcB(i) == Proc(i) /\ TicketBound'

Spec ==
    /\ Init
    /\ [][NextB]_vars
    /\ \A i \in Proc : WF_vars(ProcB(i))

=============================================================================