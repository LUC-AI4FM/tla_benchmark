------------------------------- MODULE BakeryAlgorithm -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NumProcesses, MaxTicket

VARIABLES state, ticket, choosing

(* --algorithm bakery
variables 
  state = [p \in 1..NumProcesses |-> "idle"],
  ticket = [p \in 1..NumProcesses |-> 0],
  choosing = [p \in 1..NumProcesses |-> FALSE];

process p \in 1..NumProcesses
begin
Choose:
  if
    /\ state[p] = "idle"
    /\ \/ \E q \in 1..NumProcesses : state[q] = "critical"
       \/ \E q \in 1..NumProcesses : state[q] = "waiting" 
  then
    choosing[p] := TRUE;
    ticket[p] := 1 + Max({ticket[q] | q \in 1..NumProcesses}) ;
    choosing[p] := FALSE;
    state[p] := "waiting";
  end if;

RequestCS:
  if
    /\ state[p] = "waiting"
    /\ \A q \in 1..NumProcesses \ {p} :
         \/ state[q] = "idle"
         \/ ticket[p] < ticket[q]
         \/ /\ ticket[p] = ticket[q]
            /\ p < q
  then
    state[p] := "critical";
  end if;

ReleaseCS:
  if state[p] = "critical" then
    state[p] := "idle";
  end if;
end process; *)
    
Init == 
  /\ state \in [1..NumProcesses -> {"idle"}]
  /\ ticket \in [1..NumProcesses -> {0}]
  /\ choosing \in [1..NumProcesses -> {FALSE}]

Next ==
  \/ \E p \in 1..NumProcesses :
     (state[p] = "idle" /\
      (\E q \in 1..NumProcesses : state[q] \in {"critical", "waiting"}) /\
      choosing' = [choosing EXCEPT ![p] = TRUE] /\
      ticket' = [ticket EXCEPT ![p] = 1 + Max({ticket[q] | q \in 1..NumProcesses})] /\
      choosing'' = [choosing' EXCEPT ![p] = FALSE] /\
      state' = [state EXCEPT ![p] = "waiting"]) 
  \/ \E p \in 1..NumProcesses :
     (state[p] = "waiting" /\
      (\A q \in 1..NumProcesses \ {p} : state[q] \in {"idle"} \/ ticket[p] < ticket[q] \/ (ticket[p] = ticket[q] /\ p < q)) /\
      state' = [state EXCEPT ![p] = "critical"])
  \/ \E p \in 1..NumProcesses :
     (state[p] = "critical" /\
      state' = [state EXCEPT ![p] = "idle"])

Spec == Init /\ [][Next]_<<state, ticket, choosing>>

MutualExclusion ==
  \A p, q \in 1..NumProcesses : 
    \/ p = q
    \/ ~ (state[p] = "critical" /\ state[q] = "critical")

MaxTicketConstraint ==
  \A p \in 1..NumProcesses : ticket[p] <= MaxTicket

Fairness ==
  WF_next(<<choosing>>)

THEOREM Spec => []MutualExclusion
THEOREM Spec => []MaxTicketConstraint
=============================================================================