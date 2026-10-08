--------------------------- MODULE Bakery ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N, MAX_TICKET
ASSUME N > 0
ASSUME MAX_TICKET >= 1

PROC == 1 .. N

VARIABLES choosing, number, state

vars == <<choosing, number, state>>

Init ==
   /\ choosing = [i \in PROC |-> FALSE]
   /\ number = [i \in PROC |-> 0]
   /\ state = [i \in PROC |-> "idle"]

StartChoosing(i) ==
   /\ i \in PROC
   /\ choosing[i] = FALSE
   /\ number[i] = 0
   /\ choosing' = [choosing EXCEPT ![i] = TRUE]
   /\ UNCHANGED <<number, state>>

FinishChoosing(i) ==
   /\ i \in PROC
   /\ choosing[i] = TRUE
   /\ LET newNum == 1 + MaxS({ number[j] : j \in PROC }) IN
      /\ newNum <= MAX_TICKET
      /\ number' = [number EXCEPT ![i] = newNum]
      /\ choosing' = [choosing EXCEPT ![i] = FALSE]
   /\ UNCHANGED state

EnterCritical(i) ==
   /\ i \in PROC
   /\ choosing[i] = FALSE
   /\ number[i] > 0
   /\ state[i] = "idle"
   /\ \A j \in PROC : j # i => ~(number[j] <> 0 /\ (number[j], j) < (number[i], i))
   /\ state' = [state EXCEPT ![i] = "critical"]
   /\ UNCHANGED <<choosing, number>>

Exit(i) ==
   /\ i \in PROC
   /\ state[i] = "critical"
   /\ state' = [state EXCEPT ![i] = "idle"]
   /\ number' = [number EXCEPT ![i] = 0]
   /\ UNCHANGED <<choosing>>

Next == \E i \in PROC : (StartChoosing(i) \/ FinishChoosing(i) \/ EnterCritical(i) \/ Exit(i))

MutualExclusion ==
   \A i, j \in PROC : i # j => ~(state[i]="critical" /\ state[j]="critical")

TicketBounded ==
   \A i \in PROC : number[i] <= MAX_TICKET

Spec == Init /\ [][Next]_vars /\ WF_{vars}[Next]

=============================================================================