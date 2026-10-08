---------------------------- MODULE SimpleCyclicController ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT MaxHistoryLength
VARIABLE mode, history, done

Init == 
  /\ mode = "mode1"
  /\ history = << >>
  /\ done = FALSE

NextMode(m) == 
  IF m = "mode1" THEN "mode2" ELSE "mode1"

Switch == 
  /\ mode /= "done"
  /\ mode' = NextMode(mode)
  /\ history' = Append(history, mode)
  /\ done' = done
  /\ UNCHANGED << >>

Stay == 
  /\ mode /= "done"
  /\ mode' = mode
  /\ history' = history
  /\ done' = done
  /\ UNCHANGED << >>

Done == 
  /\ mode' = "done"
  /\ history' = history
  /\ done' = TRUE

Next == 
  Switch \/ Stay \/ Done

Spec == Init /\ [][Next]_<<mode, history, done>>

HistoryInvariant == Len(history) <= MaxHistoryLength

Fairness == WF_(Switch, <<mode, history, done>>)

Liveness == <>done

THEOREM Spec => []HistoryInvariant
THEOREM Spec => Liveness
=============================================================================