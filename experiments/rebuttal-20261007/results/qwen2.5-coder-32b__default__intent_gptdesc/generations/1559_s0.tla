------------------------------- MODULE MutualExclusionLock -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS P1, P2
VARIABLES pc, turn, critical, history, stutter

(* --algorithm mutual_exclusion_lock
variables 
  pc = [P1 |-> "entry", P2 |-> "entry"],
  turn = 0,
  critical = [P1 |-> FALSE, P2 |-> FALSE],
  history = <<>>,
  stutter = [P1 |-> FALSE, P2 |-> FALSE];

process (p \in {P1, P2})
begin
entry:
  while TRUE do
    if pc[p] = "entry" then
      await \A q \in {P1, P2} \ {p}: pc[q] # "critical"
      stutter[p] := TRUE;
      history := Append(history, <<p, turn>>);
      pc[p] := "precritical1";
    else if pc[p] = "precritical1" then
      await \A q \in {P1, P2} \ {p}: pc[q] # "critical"
      stutter[p] := TRUE;
      pc[p] := "precritical2";
    else if pc[p] = "precritical2" then
      turn := p;
      stutter[p] := FALSE;
      pc[p] := "critical";
    end if;

  critical:
    await pc[p] = "critical"
    critical[p] := TRUE;
    skip; (* Critical section *)
    critical[p] := FALSE;
    pc[p] := "exit";

  exit:
    await pc[p] = "exit"
    pc[p] := "entry";
end process;

end algorithm *)

Init == /\ pc \in [P1 -> {"entry", "precritical1", "precritical2", "critical", "exit"}, P2 -> {"entry", "precritical1", "precritical2", "critical", "exit"}]
        /\ turn \in {0, 1}
        /\ critical \in [P1 -> BOOLEAN, P2 -> BOOLEAN]
        /\ history = <<>>
        /\ stutter \in [P1 -> BOOLEAN, P2 -> BOOLEAN]

Next == \/ \E p \in {P1, P2}:
              (pc[p] = "entry" /\ \A q \in {P1, P2} \ {p}: pc[q] # "critical") /\
              stutter' = [stutter EXCEPT ![p] = TRUE] /\
              history' = Append(history, <<p, turn>>) /\
              pc' = [pc EXCEPT ![p] = "precritical1"] /\
              UNCHANGED <<turn, critical>>
          \/ \E p \in {P1, P2}:
              (pc[p] = "precritical1" /\ \A q \in {P1, P2} \ {p}: pc[q] # "critical") /\
              stutter' = [stutter EXCEPT ![p] = TRUE] /\
              pc' = [pc EXCEPT ![p] = "precritical2"] /\
              UNCHANGED <<turn, critical, history>>
          \/ \E p \in {P1, P2}:
              (pc[p] = "precritical2") /\
              stutter' = [stutter EXCEPT ![p] = FALSE] /\
              turn' = p /\
              pc' = [pc EXCEPT ![p] = "critical"] /\
              UNCHANGED <<critical, history>>
          \/ \E p \in {P1, P2}:
              (pc[p] = "critical") /\
              critical' = [critical EXCEPT ![p] = TRUE] /\
              pc' = [pc EXCEPT ![p] = "exit"] /\
              UNCHANGED <<turn, history, stutter>>
          \/ \E p \in {P1, P2}:
              (pc[p] = "exit") /\
              pc' = [pc EXCEPT ![p] = "entry"] /\
              UNCHANGED <<critical, turn, history, stutter>>

Spec == Init /\ [][Next]_<<pc, turn, critical, history, stutter>>

MutualExclusion ==
  \/ \A p \in {P1, P2}: critical[p]
  \/ \E p, q \in {P1, P2} \ {p}: critical[p] /\ critical[q]

StutterInvariant ==
  \/ \A p \in {P1, P2}: stutter[p] => (pc[p] = "entry" \/ pc[p] = "precritical1" \/ pc[p] = "precritical2")

HistoryInvariant ==
  \/ \A p \in {P1, P2}:
      critical[p] /\ stutter[p] =>
        (\E i \in DOMAIN history: history[i] = <<p, turn>>)

TypeInvariants ==
  /\ pc \in [P1 -> {"entry", "precritical1", "precritical2", "critical", "exit"}, P2 -> {"entry", "precritical1", "precritical2", "critical", "exit"}]
  /\ turn \in {0, 1}
  /\ critical \in [P1 -> BOOLEAN, P2 -> BOOLEAN]
  /\ history \in SUBSEQ({<<p, t>>: p \in {P1, P2}, t \in {0, 1}})
  /\ stutter \in [P1 -> BOOLEAN, P2 -> BOOLEAN]

Invariants == \/ MutualExclusion
              \/ StutterInvariant
              \/ HistoryInvariant
              \/ TypeInvariants

Liveness ==
  WF_next(<<pc, turn, critical, history, stutter>>)

Refinement ==
  \A p \in {P1, P2}:
    (critical[p] => (\E i \in DOMAIN history: history[i] = <<p, turn>>) /\ turn = Other(p))
    /\ (stutter[p] => pc[p] \in {"entry", "precritical1", "precritical2"})

SpecWithInvariants == Spec /\ []Invariants

RefinementSpec ==
  SpecWithInvariants /\ Liveness /\ Refinement
=============================================================================