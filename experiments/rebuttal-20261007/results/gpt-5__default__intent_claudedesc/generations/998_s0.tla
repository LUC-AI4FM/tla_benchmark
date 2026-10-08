------------------------------ MODULE ResourceAllocator ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Clients, Resources

VARIABLES Held, Req, Sched

Elems(s) == { s[i] : i \in 1..Len(s) }

InSeq(s, x) == \E i \in 1..Len(s) : s[i] = x

Index(s, x) ==
  IF InSeq(s, x) THEN CHOOSE i \in 1..Len(s) : s[i] = x ELSE 0

Before(s, x) ==
  IF InSeq(s, x) THEN { s[i] : i \in 1..(Index(s, x) - 1) } ELSE {}

NoDup(s) == \A i, j \in 1..Len(s) : (i # j) => s[i] # s[j]

IsPermutationOf(ns, X) == NoDup(ns) /\ Elems(ns) = X

Remove(s, x) ==
  IF InSeq(s, x) THEN
    LET i == Index(s, x) IN
      SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))
  ELSE s

AllHeld == UNION { Held[c] : c \in Clients }

Need(c) == Req[c] \ Held[c]

Pending(c) == (Req[c] # {}) /\ (Need(c) # {})

RequestedEarlier(c) == UNION { Req[d] : d \in Before(Sched, c) }

UnscheduledPending == { c \in Clients : Pending(c) /\ ~InSeq(Sched, c) }

TypeOK ==
  /\ Held \in [Clients -> SUBSET Resources]
  /\ Req  \in [Clients -> SUBSET Resources]
  /\ Sched \in Seq(Clients)
  /\ NoDup(Sched)
  /\ Elems(Sched) \subseteq Clients

Init ==
  /\ TypeOK
  /\ \A c \in Clients : Held[c] = {}
  /\ \A c \in Clients : Req[c] = {}
  /\ Sched = << >>

RequestAct ==
  \E c \in Clients, S \in SUBSET Resources :
    /\ Req[c] = {}
    /\ Held[c] = {}
    /\ S # {}
    /\ Req' = [Req EXCEPT ![c] = S]
    /\ UNCHANGED <<Held, Sched>>

ExtendSchedule ==
  \E ns \in Seq(Clients) :
    /\ IsPermutationOf(ns, UnscheduledPending)
    /\ Sched' = Sched \o ns
    /\ UNCHANGED <<Held, Req>>

Allocate ==
  \E c \in Elems(Sched), r \in Resources :
    /\ r \in Req[c]
    /\ r \notin AllHeld
    /\ r \notin RequestedEarlier(c)
    /\ Held' = [Held EXCEPT ![c] = Held[c] \cup {r}]
    /\ Req' = Req
    /\ Sched' =
         IF (Req[c] \ (Held[c] \cup {r})) = {}
         THEN Remove(Sched, c)
         ELSE Sched

ReturnEarly ==
  \E c \in Clients, r \in Held[c] :
    /\ Need(c) # {}
    /\ Held' = [Held EXCEPT ![c] = Held[c] \ {r}]
    /\ UNCHANGED <<Req, Sched>>

ReturnSatisfied ==
  \E c \in Clients, r \in Held[c] :
    /\ Need(c) = {}
    /\ Held' = [Held EXCEPT ![c] = Held[c] \ {r}]
    /\ UNCHANGED <<Req, Sched>>

CloseRequest ==
  \E c \in Clients :
    /\ Req[c] # {}
    /\ Need(c) = {}
    /\ Held[c] = {}
    /\ Req' = [Req EXCEPT ![c] = {}]
    /\ UNCHANGED <<Held, Sched>>

Next ==
  RequestAct
  \/ ExtendSchedule
  \/ Allocate
  \/ ReturnEarly
  \/ ReturnSatisfied
  \/ CloseRequest

vars == << Held, Req, Sched >>

Spec ==
  /\ Init
  /\ [] [Next]_vars
  /\ WF_vars(ExtendSchedule)
  /\ WF_vars(\E c \in Clients, r \in Resources : Allocate)
  /\ WF_vars(\E c \in Clients, r \in Resources : ReturnSatisfied)

(*
  Safety properties
*)

Exclusive ==
  \A c1, c2 \in Clients :
    (c1 # c2) => (Held[c1] \cap Held[c2] = {})

SchedClientsHaveOutstanding ==
  \A c \in Elems(Sched) : Pending(c)

SchedRespectInv ==
  \A c \in Elems(Sched) : Held[c] \cap RequestedEarlier(c) = {}

Safety == TypeOK /\ Exclusive /\ SchedClientsHaveOutstanding /\ SchedRespectInv

(*
  Liveness properties (under the fairness assumptions in Spec)
*)

AcquireLiveness ==
  \A c \in Clients : \A r \in Resources : [] ( (r \in Req[c]) => <> (r \in Held[c]) )

ReleaseLiveness ==
  \A c \in Clients : [] ( (Need(c) = {}) => <> (Held[c] = {}) )

FullySatisfied(c) == (Req[c] = {}) \/ (Need(c) = {})

FullySatisfiedInfOften ==
  \A c \in Clients : [] <> FullySatisfied(c)

Liveness == AcquireLiveness /\ ReleaseLiveness /\ FullySatisfiedInfOften

=============================================================================