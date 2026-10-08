------------------------------- MODULE TwoStateController -------------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANT MaxHist
ASSUME MaxHist \in Nat /\ MaxHist >= 1

VARIABLES mode, history, done

Modes == {M1, M2}

vars == << mode, history, done >>

TypeInv ==
  /\ mode \in Modes
  /\ history \in Seq(Modes)
  /\ Len(history) <= MaxHist
  /\ done \in BOOLEAN

Init ==
  /\ mode = M1
  /\ history = << >>
  /\ done = FALSE
  /\ TypeInv

Switch ==
  /\ ~done
  /\ Len(history) < MaxHist
  /\ mode' = IF mode = M1 THEN M2 ELSE M1
  /\ history' = Append(history, mode)
  /\ done' = done

Terminate ==
  /\ ~done
  /\ mode = M2
  /\ done' = TRUE
  /\ UNCHANGED << mode, history >>

Next == Switch \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Switch)

SafetyInvariant == Len(history) <= MaxHist
AlwaysSafety == []SafetyInvariant

TemporalGoal == <>done

=============================================================================