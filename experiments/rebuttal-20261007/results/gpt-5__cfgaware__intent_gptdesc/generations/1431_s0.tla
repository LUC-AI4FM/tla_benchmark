----------------------------- MODULE CyclicController -----------------------------
EXTENDS Naturals, Sequences

CONSTANT HistBound

VARIABLES mode, hist, done

Modes == {"A", "B"}
OtherMode(m) == IF m = "A" THEN "B" ELSE "A"

vars == << mode, hist, done >>

Init ==
  /\ mode = "A"
  /\ hist = << >>
  /\ done = FALSE

Switch ==
  /\ ~done
  /\ Len(hist) + 1 < HistBound
  /\ mode' = OtherMode(mode)
  /\ hist' = Append(hist, mode)
  /\ done' = done

Hold ==
  /\ ~done
  /\ mode' = mode
  /\ hist' = hist
  /\ done' = done

Finish ==
  /\ ~done
  /\ done' = TRUE
  /\ mode' = mode
  /\ hist' = hist

Next == Switch \/ Hold \/ Finish

TypeOK ==
  /\ mode \in Modes
  /\ hist \in Seq(Modes)
  /\ done \in BOOLEAN

HistoryBound == Len(hist) < HistBound

Invariant == TypeOK /\ HistoryBound
SafetyInv == Invariant

Terminal == done
Termination == <>Terminal
Liveness == Termination

Fairness == WF_vars(Switch)

Spec == Init /\ [][Next]_vars /\ Fairness
============================================================================