------------------------------ MODULE ResourceAllocator ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Clients, Resources

VARIABLES Req, Hold, Sched

vars == << Req, Hold, Sched >>

SeqToSet(s) == { s[i] : i \in 1..Len(s) }

NoDuplicates(s) == \A i, j \in 1..Len(s) : i # j => s[i] # s[j]

InSched(c) == c \in SeqToSet(Sched)

Pos(c, s) == CHOOSE i \in 1..Len(s) : s[i] = c

EarlierSet(c, s) ==
  LET i == Pos(c, s)
  IN { s[k] : k \in 1..(i-1) }

Take(s, n) ==
  IF n <= 0 THEN << >> ELSE [ i \in 1..n |-> s[i] ]

Drop(s, n) ==
  IF n > Len(s) THEN << >>
  ELSE [ i \in 1..(Len(s) - n + 1) |-> s[n + i - 1] ]

RemoveClient(s, c) ==
  IF c \in SeqToSet(s)
    THEN LET i == Pos(c, s) IN Take(s, i-1) \o Drop(s, i+1)
    ELSE s

IsPermutationOfSet(p, U) ==
  /\ p \in Seq(Clients)
  /\ NoDuplicates(p)
  /\ SeqToSet(p) = U

TypeOK ==
  /\ Req \in [Clients -> SUBSET Resources]
  /\ Hold \in [Clients -> SUBSET Resources]
  /\ Sched \in Seq(Clients)
  /\ NoDuplicates(Sched)

HoldSet == UNION { Hold[c] : c \in Clients }
Available == Resources \ HoldSet

Need(c) == Req[c] \ Hold[c]
Pending(c) == Need(c) # {}

UnionReq(S) == UNION { Req[c] : c \in S }
UnionHold(S) == UNION { Hold[c] : c \in S }

Init ==
  /\ TypeOK
  /\ \A c \in Clients : Req[c] = {}
  /\ \A c \in Clients : Hold[c] = {}
  /\ Sched = << >>

ClientRequest(c, rset) ==
  /\ c \in Clients
  /\ Req[c] = {}
  /\ Hold[c] = {}
  /\ rset \subseteq Resources
  /\ rset # {}
  /\ Req' = [Req EXCEPT ![c] = rset]
  /\ UNCHANGED << Hold, Sched >>

AllocateSome(c, x) ==
  /\ c \in Clients
  /\ InSched(c)
  /\ x \subseteq Need(c)
  /\ x \subseteq Available
  /\ x # {}
  /\ LET earlier == EarlierSet(c, Sched)
     IN x \cap UnionReq(earlier) = {}
  /\ Hold' = [Hold EXCEPT ![c] = @ \cup x]
  /\ UNCHANGED << Req, Sched >>

AllocateAny(c) == \E x \in SUBSET Resources : AllocateSome(c, x)

ReturnSome(c, x) ==
  /\ c \in Clients
  /\ Hold[c] # Req[c]
  /\ x \subseteq Hold[c]
  /\ x # {}
  /\ Hold' = [Hold EXCEPT ![c] = @ \ x]
  /\ UNCHANGED << Req, Sched >>

ReleaseSatisfied(c) ==
  /\ c \in Clients
  /\ Req[c] # {}
  /\ Hold[c] = Req[c]
  /\ Hold' = [Hold EXCEPT ![c] = {}]
  /\ Req' = [Req EXCEPT ![c] = {}]
  /\ Sched' = RemoveClient(Sched, c)

ScheduleOne(c) ==
  /\ c \in Clients
  /\ ~InSched(c)
  /\ Pending(c)
  /\ Sched' = Sched \o << c >>
  /\ UNCHANGED << Req, Hold >>

AppendPermutation ==
  /\ LET U == { d \in Clients : Pending(d) /\ ~InSched(d) }
     IN /\ U # {}
        /\ \E p \in Seq(Clients) :
             /\ IsPermutationOfSet(p, U)
             /\ Sched' = Sched \o p
  /\ UNCHANGED << Req, Hold >>

Next ==
  \/ \E c \in Clients, rset \in SUBSET Resources : ClientRequest(c, rset)
  \/ \E c \in Clients, x \in SUBSET Resources : AllocateSome(c, x)
  \/ \E c \in Clients, x \in SUBSET Resources : ReturnSome(c, x)
  \/ \E c \in Clients : ReleaseSatisfied(c)
  \/ \E c \in Clients : ScheduleOne(c)
  \/ AppendPermutation

Fairness ==
  /\ \A c \in Clients : SF_vars(ScheduleOne(c))
  /\ \A c \in Clients : SF_vars(AllocateAny(c))
  /\ \A c \in Clients : WF_vars(ReleaseSatisfied(c))

Spec == Init /\ [][Next]_vars /\ Fairness

SafetyExclusive ==
  \A c1, c2 \in Clients : c1 # c2 => Hold[c1] \cap Hold[c2] = {}

SafetySchedOutstanding ==
  \A c \in SeqToSet(Sched) : Req[c] # {}

SafetySchedFeasible ==
  \A c \in SeqToSet(Sched) :
    Need(c) \subseteq Available
             \cup UnionReq(EarlierSet(c, Sched))
             \cup UnionHold(EarlierSet(c, Sched))

Safety == SafetyExclusive /\ SafetySchedOutstanding /\ SafetySchedFeasible

FullSat(c) == Req[c] = Hold[c]

LivenessRequestSatisfied ==
  \A c \in Clients : [](Req[c] # {} => <> FullSat(c))

LivenessReleaseAfterSatisfied ==
  \A c \in Clients : []((FullSat(c) /\ Req[c] # {}) => <> (Req[c] = {} /\ Hold[c] = {}))

LivenessFullySatisfiedInfOften ==
  \A c \in Clients : []<>(FullSat(c))

Liveness == LivenessRequestSatisfied /\ LivenessReleaseAfterSatisfied /\ LivenessFullySatisfiedInfOften

=============================================================================