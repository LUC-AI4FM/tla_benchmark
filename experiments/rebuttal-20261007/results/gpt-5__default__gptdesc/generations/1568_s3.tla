------------------------------ MODULE Bakery ------------------------------

EXTENDS Naturals

CONSTANTS
  NumProcs, \* Number of processes (fixed, positive)
  MaxTicket  \* Maximum ticket value used as a TLC bound

ASSUME /\ NumProcs \in Nat \ {0}
       /\ MaxTicket \in Nat \ {0}

ProcSet == 1..NumProcs

VARIABLES
  pc,        \* program counter per process
  choosing,  \* choosing flag per process
  number,    \* ticket number per process
  j          \* loop index for waiting over other processes

vars == << pc, choosing, number, j >>

(*
  Lexicographic order on pairs (number[i], i)
  i has priority over k if number[i] < number[k],
  or equal tickets and i < k.
*)
LexLt(i, k) == number[i] < number[k] \/ (number[i] = number[k] /\ i < k)

(*
  Maximum of a finite set of natural numbers (0 for the empty set).
*)
MaxOf(S) == IF S = {} THEN 0 ELSE CHOOSE m \in S: \A n \in S: n <= m

Init ==
  /\ pc = [i \in ProcSet |-> "start"]
  /\ choosing = [i \in ProcSet |-> FALSE]
  /\ number = [i \in ProcSet |-> 0]
  /\ j = [i \in ProcSet |-> 1]

(*
  The per-process action, following the PlusCal translation of Lamport's Bakery algorithm.
*)
Proc(i) ==
  \/ /\ pc[i] = "start"
     /\ choosing' = [choosing EXCEPT ![i] = TRUE]
     /\ pc' = [pc EXCEPT ![i] = "choose2"]
     /\ UNCHANGED << number, j >>
  \/ /\ pc[i] = "choose2"
     /\ LET S == { number[p] : p \in ProcSet } IN
        number' = [number EXCEPT ![i] = MaxOf(S) + 1]
     /\ pc' = [pc EXCEPT ![i] = "choose3"]
     /\ UNCHANGED << choosing, j >>
  \/ /\ pc[i] = "choose3"
     /\ choosing' = [choosing EXCEPT ![i] = FALSE]
     /\ j' = [j EXCEPT ![i] = 1]
     /\ pc' = [pc EXCEPT ![i] = "wait"]
     /\ UNCHANGED number
  \/ /\ pc[i] = "wait" /\ j[i] = i
     /\ j' = [j EXCEPT ![i] = j[i] + 1]
     /\ UNCHANGED << choosing, number, pc >>
  \/ /\ pc[i] = "wait" /\ j[i] # i /\ j[i] <= NumProcs
     /\ ~choosing[j[i]]
     /\ number[j[i]] = 0 \/ LexLt(i, j[i])
     /\ j' = [j EXCEPT ![i] = j[i] + 1]
     /\ UNCHANGED << choosing, number, pc >>
  \/ /\ pc[i] = "wait" /\ j[i] > NumProcs
     /\ pc' = [pc EXCEPT ![i] = "cs"]
     /\ UNCHANGED << choosing, number, j >>
  \/ /\ pc[i] = "cs"
     /\ number' = [number EXCEPT ![i] = 0]
     /\ pc' = [pc EXCEPT ![i] = "start"]
     /\ UNCHANGED << choosing, j >>

Next == \E i \in ProcSet: Proc(i)

Spec == Init /\ [][Next]_vars /\ \A i \in ProcSet: WF_vars(Proc(i))

(*
  Safety invariants
*)
TypeOK ==
  /\ pc \in [ProcSet -> {"start", "choose2", "choose3", "wait", "cs"}]
  /\ choosing \in [ProcSet -> BOOLEAN]
  /\ number \in [ProcSet -> Nat]
  /\ j \in [ProcSet -> 1..(NumProcs + 1)]

MutualExclusion ==
  \A i, k \in ProcSet: i # k => ~(pc[i] = "cs" /\ pc[k] = "cs")

(*
  Ticket bound constraint for TLC model checking.
  TLC can check this as an invariant; it can also be used as a state constraint in the config.
*)
TicketBound ==
  \A i \in ProcSet: number[i] <= MaxTicket

=============================================================================