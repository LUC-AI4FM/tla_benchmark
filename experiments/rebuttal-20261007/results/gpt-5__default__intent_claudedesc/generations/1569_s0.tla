----------------------------- MODULE Bakery -----------------------------
EXTENDS Naturals

CONSTANTS N, MaxTicket

Proc == 1..N

Max2(a, b) == IF a >= b THEN a ELSE b

VARIABLES
  choosing,   \* [Proc -> BOOLEAN]
  ticket,     \* [Proc -> 0..MaxTicket]
  pc,         \* [Proc -> {"Idle","Read","Wait","CS"}]
  readSet,    \* [Proc -> SUBSET Proc]
  maxSeen,    \* [Proc -> 0..MaxTicket]
  waitSet     \* [Proc -> SUBSET Proc]

vars == << choosing, ticket, pc, readSet, maxSeen, waitSet >>

Other(i) == Proc \ {i}

Ahead(i, j) ==
  /\ ticket[j] # 0
  /\ (ticket[j] < ticket[i] \/ (ticket[j] = ticket[i] /\ j < i))

TypeOK ==
  /\ choosing \in [Proc -> BOOLEAN]
  /\ ticket \in [Proc -> 0..MaxTicket]
  /\ pc \in [Proc -> {"Idle","Read","Wait","CS"}]
  /\ readSet \in [Proc -> SUBSET Proc]
  /\ maxSeen \in [Proc -> 0..MaxTicket]
  /\ waitSet \in [Proc -> SUBSET Proc]

Init ==
  /\ choosing = [i \in Proc |-> FALSE]
  /\ ticket   = [i \in Proc |-> 0]
  /\ pc       = [i \in Proc |-> "Idle"]
  /\ readSet  = [i \in Proc |-> {}]
  /\ maxSeen  = [i \in Proc |-> 0]
  /\ waitSet  = [i \in Proc |-> {}]

StartChoosing(i) ==
  /\ i \in Proc
  /\ pc[i] = "Idle"
  /\ ~choosing[i]
  /\ ticket[i] = 0
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ readSet'  = [readSet EXCEPT ![i] = Other(i)]
  /\ maxSeen'  = [maxSeen EXCEPT ![i] = 0]
  /\ pc'       = [pc EXCEPT ![i] = "Read"]
  /\ UNCHANGED << ticket, waitSet >>

ReadOne(i, j) ==
  /\ i \in Proc /\ j \in Proc
  /\ pc[i] = "Read"
  /\ j \in readSet[i]
  /\ ~choosing[j]
  /\ readSet' = [readSet EXCEPT ![i] = @ \ {j}]
  /\ maxSeen' = [maxSeen EXCEPT ![i] = Max2(@, ticket[j])]
  /\ UNCHANGED << choosing, ticket, waitSet, pc >>

AssignTicket(i) ==
  /\ i \in Proc
  /\ pc[i] = "Read"
  /\ readSet[i] = {}
  /\ maxSeen[i] + 1 <= MaxTicket
  /\ ticket'  = [ticket EXCEPT ![i] = maxSeen[i] + 1]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ waitSet' = [waitSet EXCEPT ![i] = Other(i)]
  /\ pc'      = [pc EXCEPT ![i] = "Wait"]
  /\ UNCHANGED << readSet, maxSeen >>

WaitRemove(i, j) ==
  /\ i \in Proc /\ j \in Proc
  /\ pc[i] = "Wait"
  /\ ticket[i] > 0
  /\ j \in waitSet[i]
  /\ ~choosing[j]
  /\ ~Ahead(i, j)
  /\ waitSet' = [waitSet EXCEPT ![i] = @ \ {j}]
  /\ UNCHANGED << choosing, ticket, readSet, maxSeen, pc >>

EnterCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "Wait"
  /\ ticket[i] > 0
  /\ waitSet[i] = {}
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << choosing, ticket, readSet, maxSeen, waitSet >>

ExitCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "CS"
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ pc' = [pc EXCEPT ![i] = "Idle"]
  /\ UNCHANGED << choosing, readSet, maxSeen, waitSet >>

Next ==
  \E i \in Proc:
    StartChoosing(i)
    \/ (\E j \in Proc: ReadOne(i, j))
    \/ AssignTicket(i)
    \/ (\E j \in Proc: WaitRemove(i, j))
    \/ EnterCS(i)
    \/ ExitCS(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in Proc: (i # j) => ~(pc[i] = "CS" /\ pc[j] = "CS")

TicketBound ==
  \A i \in Proc: ticket[i] \in 0..MaxTicket
=============================================================================