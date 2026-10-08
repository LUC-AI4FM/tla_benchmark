----------------------------- MODULE Bakery -----------------------------
EXTENDS Naturals, TLC, FiniteSets

(*
  Lamport's Bakery mutual-exclusion algorithm for an arbitrary finite set of threads Procs.
  Ticket values are bounded by the constant MaxTicket for model checking.

  Fairness assumption: per-thread weak fairness on the thread-local action Proc(p).
*)

CONSTANTS
  Procs,      \* finite set of thread identifiers; assumed to be a subset of Nat
  MaxTicket   \* maximum ticket value (a positive integer bound)

ASSUME /\ Procs \subseteq Nat
       /\ MaxTicket \in Nat /\ MaxTicket > 0

(*
  Number of processes (exposed for configuration binding).
*)
NumProcs == Cardinality(Procs)

VARIABLES
  choosing,   \* [p \in Procs -> BOOLEAN]
  ticket,     \* [p \in Procs -> 0..MaxTicket], where 0 means "not trying"
  pc          \* [p \in Procs -> {"idle","take","post","wait","cs"}]

vars == << choosing, ticket, pc >>

\* Type correctness
TypeOK ==
  /\ choosing \in [Procs -> BOOLEAN]
  /\ ticket \in [Procs -> 0..MaxTicket]
  /\ pc \in [Procs -> {"idle","take","post","wait","cs"}]

\* Initial state: everyone idle, not choosing, no ticket.
Init ==
  /\ choosing = [p \in Procs |-> FALSE]
  /\ ticket   = [p \in Procs |-> 0]
  /\ pc       = [p \in Procs |-> "idle"]

\* Helper definitions
CS(p) == pc[p] = "cs"

TicketSet == { ticket[q] : q \in Procs }
MaxSeen == IF TicketSet = {} THEN 0 ELSE Max(TicketSet)

Other(p) == Procs \ {p}

\* Lexicographic priority: p precedes q if its ticket is smaller,
\* or equal but with smaller id (natural-number thread ids).
PriorLE(p,q) == ticket[p] < ticket[q] \/ (ticket[p] = ticket[q] /\ p < q)

\* Waiting condition: p can enter iff no q has priority over p,
\* and no q is still choosing.
WaitOK(p) ==
  \A q \in Other(p) :
    /\ ~choosing[q]
    /\ ( ticket[q] = 0 \/ PriorLE(p,q) )

\* Thread-local actions
ChooseStart(p) ==
  /\ p \in Procs
  /\ pc[p] = "idle"
  /\ choosing' = [choosing EXCEPT ![p] = TRUE]
  /\ ticket'   = ticket
  /\ pc'       = [pc EXCEPT ![p] = "take"]

TakeTicket(p) ==
  /\ p \in Procs
  /\ pc[p] = "take"
  /\ LET S == { ticket[q] : q \in Procs }
         m == IF S = {} THEN 0 ELSE Max(S)
     IN /\ m < MaxTicket
        /\ ticket'   = [ticket EXCEPT ![p] = m + 1]
        /\ choosing' = choosing
        /\ pc'       = [pc EXCEPT ![p] = "post"]

FinishChoosing(p) ==
  /\ p \in Procs
  /\ pc[p] = "post"
  /\ choosing' = [choosing EXCEPT ![p] = FALSE]
  /\ ticket'   = ticket
  /\ pc'       = [pc EXCEPT ![p] = "wait"]

EnterCS(p) ==
  /\ p \in Procs
  /\ pc[p] = "wait"
  /\ WaitOK(p)
  /\ choosing' = choosing
  /\ ticket'   = ticket
  /\ pc'       = [pc EXCEPT ![p] = "cs"]

ExitCS(p) ==
  /\ p \in Procs
  /\ pc[p] = "cs"
  /\ choosing' = choosing
  /\ ticket'   = [ticket EXCEPT ![p] = 0]
  /\ pc'       = [pc EXCEPT ![p] = "idle"]

\* Per-process step and global next-state relation
Proc(p) == ChooseStart(p) \/ TakeTicket(p) \/ FinishChoosing(p) \/ EnterCS(p) \/ ExitCS(p)

Next == \E p \in Procs : Proc(p)

\* Safety: at most one thread in the critical section
MutualExclusion ==
  Cardinality({ p \in Procs : CS(p) }) <= 1

\* Boundedness: tickets remain within the declared bound
TicketBound == \A p \in Procs : ticket[p] \in 0..MaxTicket

\* Combined state invariant (exposed for configuration binding)
Invariant == TypeOK /\ MutualExclusion /\ TicketBound

\* Liveness/progress: any thread that is attempting eventually enters CS
Attempting(p) ==
  \/ choosing[p]
  \/ ticket[p] # 0
  \/ pc[p] \in {"take","post","wait"}

Progress ==
  \A p \in Procs : [] ( Attempting(p) => <> CS(p) )

\* Absence of global deadlock while someone is trying
NoGlobalDeadlock ==
  [] ( ( \E p \in Procs : Attempting(p) ) => ENABLED Next )

\* Specification: initial condition, next-state relation under weak fairness per process
Fairness == \A p \in Procs : WF_vars(Proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness
=============================================================================