```tla
MODULE BakeryAlgorithm

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS NumProcesses, MaxTicketValue

VARIABLES state, ticket, choosing

(* --algorithm bakery
variables state = [p \in 1..NumProcesses |-> "idle"],
          ticket = [p \in 1..NumProcesses |-> 0],
          choosing = [p \in 1..NumProcesses |-> FALSE];

process p \in 1..NumProcesses
begin
  while TRUE do
    choosing[p] := TRUE;
    ticket[p] := 1 + Max({ticket[q] : q \in 1..NumProcesses});
    choosing[p] := FALSE;

    /\ await \A q \in 1..NumProcesses \ {p} :
         ~choosing[q] \/ <ticket[q], q> << <ticket[p], p>;
    
    state[p] := "critical";
    state[p] := "idle";
end process;
--algorithm *)

Init == 
  /\ state = [p \in 1..NumProcesses |-> "idle"]
  /\ ticket = [p \in 1..NumProcesses |-> 0]
  /\ choosing = [p \in 1..NumProcesses |-> FALSE]

Next ==
  \E p \in 1..NumProcesses :
    \/ /\ choosing' = [choosing EXCEPT ![p] = TRUE]
       /\ ticket' = [ticket EXCEPT ![p] = 1 + Max({ticket[q] : q \in 1..NumProcesses})]
       /\ state' = state
    \/ /\ choosing' = [choosing EXCEPT ![p] = FALSE]
       /\ ticket' = ticket
       /\ state' = state
    \/ /\ \A q \in 1..NumProcesses \ {p} : ~choosing[q] \/ <ticket[q], q> << <ticket[p], p>
       /\ choosing' = choosing
       /\ ticket' = ticket
       /\ state' = [state EXCEPT ![p] = "critical"]
    \/ /\ state' = [state EXCEPT ![p] = "idle"]
       /\ choosing' = choosing
       /\ ticket' = ticket

Spec ==
  Init /\ [][Next]_<<choosing, ticket, state>> 

(\* Invariants \*)
Inv1 == \A p, q \in 1..NumProcesses : p # q => ~ (state[p] = "critical" /\ state[q] = "critical")

Inv2 == \A p \in 1..NumProcesses : ticket[p] \leq MaxTicketValue

(\* Fairness \*)
WF_choosing ==
  WF_any([p \in 1..NumProcesses |-> <<choosing, ticket, state>>], choosing)

SpecWithInvariantsAndFairness ==
  Spec /\ Inv1 /\ Inv2 /\ WF_choosing
```