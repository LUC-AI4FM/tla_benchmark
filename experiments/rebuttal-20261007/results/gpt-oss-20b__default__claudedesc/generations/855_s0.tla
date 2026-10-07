MODULE PrisonersSwitches
EXTENDS Naturals, Sequences, TLC, SETS

CONSTANTS Prisoner, Counter
ASSUME Counter \in Prisoner

VARIABLES switchAUp, switchBUp, timesSwitched, count, done

TypeInvariant ==
  /\ switchAUp ∈ BOOLEAN
  /\ switchBUp ∈ BOOLEAN
  /\ timesSwitched ∈ [Prisoner \ {Counter} -> 0..2]
  /\ count ∈ Nat
  /\ done ∈ BOOLEAN

Init ==
  /\ TypeInvariant
  /\ switchAUp = FALSE
  /\ switchBUp ∈ BOOLEAN
  /\ timesSwitched = [p \in Prisoner \ {Counter} |-> 0]
  /\ count = 0
  /\ done = FALSE

NonCounterAction(p) ==
  /\ p ∈ Prisoner \ {Counter}
  /\ (switchAUp /\ 
        /\ switchBUp' = ~switchBUp
        /\ switchAUp' = switchAUp
        /\ timesSwitched' = [timesSwitched EXCEPT ![p] = timesSwitched[p]] )
   \/ (~switchAUp /\ timesSwitched[p] < 2) /\
        /\ switchAUp' = TRUE
        /\ timesSwitched' = [timesSwitched EXCEPT ![p] = timesSwitched[p]+1]
        /\ switchBUp' = switchBUp

CounterAction ==
  /\ Counter ∈ Prisoner
  /\ (switchAUp /\ 
        /\ switchAUp' = FALSE
        /\ count' = count + 1
        /\ switchBUp' = switchBUp )
   \/ (~switchAUp /\
        /\ switchBUp' = ~switchBUp
        /\ switchAUp' = switchAUp
        /\ count' = count)

DoneAction ==
  /\ done' = IF count' >= 2 * (Cardinality(Prisoner) - 1) THEN TRUE ELSE done

Next ==
  \E p ∈ Prisoner :
    LET action == IF p = Counter THEN CounterAction ELSE NonCounterAction(p)
    IN
      /\ action
      /\ DoneAction

CountInvariant ==
  count = SUM p ∈ Prisoner \ {Counter} : timesSwitched[p] - IF switchAUp THEN 1 ELSE 0

Safety ==
  Implies(done, \A p ∈ Prisoner \ {Counter}: timesSwitched[p] >= 1)

Liveness ==
  <> done

Spec == Init /\ [][Next]_<<switchAUp, switchBUp, timesSwitched, count, done>> 
        /\ WF_vars(Next) /\ Safety /\ CountInvariant

TypeOK == TypeInvariant
CountInv == CountInvariant

END MODULE