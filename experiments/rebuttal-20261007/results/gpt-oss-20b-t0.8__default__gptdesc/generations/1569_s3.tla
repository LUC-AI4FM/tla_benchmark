MODULE Bakery
EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES ticket, choosing, pc, localRead, maxValue, nextProcess

(* ---------- Types and Initial Conditions ---------- *)
TypeOK ==
  /\ ticket \in [1..N -> Nat]
  /\ choosing \in [1..N -> BOOLEAN]
  /\ pc \in [1..N -> {"Start","ChoosingTicket","Waiting","CriticalSection","Exit"}]
  /\ localRead \in [1..N -> SUBSET 1..N]
  /\ maxValue \in [1..N -> Nat]
  /\ nextProcess \in [1..N -> 1..N]

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ choosing = [i \in 1..N |-> FALSE]
  /\ pc = [i \in 1..N |-> "Start"]
  /\ localRead = [i \in 1..N |-> {}]
  /\ maxValue = [i \in 1..N |-> 0]
  /\ nextProcess = [i \in 1..N |-> 1]
  /\ TypeOK

(* ---------- Helper Functions ---------- *)
MaxTicket(snapshot) == Max([j \in 1..N |-> snapshot[j]])

(* ---------- Actions for Process i ---------- *)
ChooseTicket(i) ==
  /\ pc[i] = "Start"
  /\ choosing[i] = FALSE
  /\ ticket' = ticket
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ localRead' = [localRead EXCEPT ![i] = ticket]
  /\ maxValue' = [maxValue EXCEPT ![i] = MaxTicket(ticket)]
  /\ nextProcess' = [nextProcess EXCEPT ![i] = 1]
  /\ pc'[i] = "ChoosingTicket"

TicketSet(i) ==
  /\ pc[i] = "ChoosingTicket"
  /\ ticket' = [ticket EXCEPT ![i] = maxValue[i]+1]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ pc'[i] = "Waiting"

WaitAction(i) ==
  /\ pc[i] = "Waiting"
  /\ \A j \in 1..N : j /= i => NOT (ticket[j] > 0 /\ (ticket[j], j) < (ticket[i], i))
  /\ ticket' = ticket
  /\ choosing' = choosing
  /\ localRead' = localRead
  /\ maxValue' = maxValue
  /\ nextProcess' = nextProcess
  /\ pc'[i] = "CriticalSection"

EnterCS(i) ==
  /\ pc[i] = "CriticalSection"
  /\ pc'[i] = "Exit"
  /\ ticket' = ticket
  /\ choosing' = choosing
  /\ localRead' = localRead
  /\ maxValue' = maxValue
  /\ nextProcess' = nextProcess

ExitAction(i) ==
  /\ pc[i] = "Exit"
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ pc'[i] = "Start"
  /\ choosing' = choosing
  /\ localRead' = localRead
  /\ maxValue' = maxValue
  /\ nextProcess' = nextProcess

(* ---------- Next State Relation ---------- *)
Next ==
  \E i \in 1..N :
    ChooseTicket(i) \/ TicketSet(i) \/ WaitAction(i) \/ EnterCS(i) \/ ExitAction(i)

(* ---------- Invariants ---------- *)
MutualExclusion ==
  \A i, j \in 1..N : (pc[i] = "CriticalSection" /\ pc[j] = "CriticalSection") => i = j

TicketBoundInvariant ==
  \A i \in 1..N : ticket[i] <= N

(* ---------- Specification ---------- *)
Spec == Init
        /\ [][Next]_(<<ticket, choosing, pc, localRead, maxValue, nextProcess>>)
        /\ WF_vars(Next)
        /\ MutualExclusion

(* ---------- State Constraint for TLC ---------- *)
StateConstraint == TicketBoundInvariant

===============================================================================