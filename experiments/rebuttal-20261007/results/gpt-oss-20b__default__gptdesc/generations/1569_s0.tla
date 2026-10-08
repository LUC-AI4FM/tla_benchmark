MODULE Bakery
EXTENDS Naturals, TLC

CONSTANTS N, MaxTicketBound

VARIABLES tickets, choosing, state, readSet, maxTicket, nextProcess

Proc == 1..N

Init ==
  /\ tickets = [p \in Proc |-> 0]
  /\ choosing = [p \in Proc |-> FALSE]
  /\ state   = [p \in Proc |-> "idle"]
  /\ readSet = [p \in Proc |-> {}]
  /\ maxTicket = [p \in Proc |-> 0]
  /\ nextProcess = [p \in Proc |-> p]

Choose(p) ==
  /\ state[p] = "idle"
  /\ choosing'   = [choosing EXCEPT ![p] = TRUE]
  /\ state'      = [state EXCEPT ![p] = "choosing"]
  /\ readSet'    = [readSet EXCEPT ![p] = {}]
  /\ maxTicket'  = [maxTicket EXCEPT ![p] = 0]
  /\ nextProcess'= [nextProcess EXCEPT ![p] = p]
  /\ tickets'    = tickets

ComputeTicket(p) ==
  /\ state[p] = "choosing"
  /\ choosing'   = [choosing EXCEPT ![p] = FALSE]
  /\ tickets'    = [tickets EXCEPT ![p] = 1 + MAX(\{tickets[q] : q \in Proc\})]
  /\ state'      = [state EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<readSet, maxTicket, nextProcess>>

WaitAction(p) ==
  /\ state[p] = "waiting"
  /\ (\A j \in Proc :
        (j # p) => ~(choosing[j] \/ (tickets[j] < tickets[p]) \/ (tickets[j] = tickets[p] /\ j < p)))
  /\ state'      = [state EXCEPT ![p] = "critical"]
  /\ UNCHANGED <<tickets, choosing, readSet, maxTicket, nextProcess>>

ExitAction(p) ==
  /\ state[p] = "critical"
  /\ tickets'    = [tickets EXCEPT ![p] = 0]
  /\ state'      = [state EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<choosing, readSet, maxTicket, nextProcess>>

Next == \E p \in Proc :
          Choose(p) \/ ComputeTicket(p) \/ WaitAction(p) \/ ExitAction(p)

MutualExcl ==
  \A p, q \in Proc : (state[p] = "critical" /\ state[q] = "critical") => p = q

TicketBoundInv ==
  \A p \in Proc : tickets[p] <= MaxTicketBound

Spec == Init /\ [][Next]_<<tickets, choosing, state, readSet, maxTicket, nextProcess>> /\ MutualExcl /\ TicketBoundInv
