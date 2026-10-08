---- MODULE Bakery ----
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS Proc, MaxTicket

ASSUME
  /\ Proc \subseteq Nat
  /\ Proc /= {}
  /\ MaxTicket \in Nat \ {0}

VARIABLES pc, choosing, number

vars == << pc, choosing, number >>

PCStates == {"idle", "choose", "assign", "finish", "wait", "cs"}

TypeInv ==
  /\ pc \in [Proc -> PCStates]
  /\ choosing \in [Proc -> BOOLEAN]
  /\ number \in [Proc -> 0..MaxTicket]

Init ==
  /\ pc = [p \in Proc |-> "idle"]
  /\ choosing = [p \in Proc |-> FALSE]
  /\ number = [p \in Proc |-> 0]
  /\ TypeInv

LexLess(p, q) ==
  number[p] < number[q] \/ (number[p] = number[q] /\ p < q)

CanEnter(p) ==
  \A q \in Proc:
       q = p
    \/ (~choosing[q] /\ (number[q] = 0 \/ LexLess(p, q)))

Try(p) ==
  /\ pc[p] = "idle"
  /\ choosing' = [choosing EXCEPT ![p] = TRUE]
  /\ pc' = [pc EXCEPT ![p] = "choose"]
  /\ UNCHANGED number

Assign(p) ==
  /\ pc[p] = "choose"
  /\ LET m == Max({ number[q] : q \in Proc })
     IN number' = [number EXCEPT ![p] =
                      IF m + 1 <= MaxTicket THEN m + 1 ELSE MaxTicket]
  /\ pc' = [pc EXCEPT ![p] = "assign"]
  /\ UNCHANGED choosing

FinishChoose(p) ==
  /\ pc[p] = "assign"
  /\ choosing' = [choosing EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "wait"]
  /\ UNCHANGED number

EnterCS(p) ==
  /\ pc[p] = "wait"
  /\ CanEnter(p)
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED << choosing, number >>

ExitCS(p) ==
  /\ pc[p] = "cs"
  /\ number' = [number EXCEPT ![p] = 0]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED choosing

Step(p) == Try(p) \/ Assign(p) \/ FinishChoose(p) \/ EnterCS(p) \/ ExitCS(p)

Next == \E p \in Proc: Step(p)

InCS(p) == pc[p] = "cs"
Trying(p) == pc[p] \in {"choose", "assign", "finish", "wait"}

MutualExclusion ==
  Cardinality({ p \in Proc : InCS(p) }) <= 1

BoundedTickets ==
  \A p \in Proc: number[p] \in 0..MaxTicket

Safety == []MutualExclusion
Boundedness == []BoundedTickets

NoDeadlock ==
  []( (\E p \in Proc: Trying(p)) => Enabled(Next) )

StarvationFree ==
  \A p \in Proc: ( []<>(Trying(p)) => []<>(InCS(p)) )

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc: WF_vars(Step(p))

====