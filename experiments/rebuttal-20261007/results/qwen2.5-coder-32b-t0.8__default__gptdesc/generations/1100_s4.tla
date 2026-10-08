```tla
 MODULE MutualExclusionLock

EXTENDS Integers, TLC, PlusCal

CONSTANTS P1, P2

VARIABLES turn, pc, loc

Init == 
  /\ turn = P1 
  /\ pc = [P1 |-> "non-critical", P2 |-> "non-critical"]
  /\ loc = [P1 |-> "non-critical", P2 |-> "non-critical"]

Next == 
  \/ \E p \in {P1, P2}:
      /\ pc[p] = "non-critical"
      /\ pc' = [pc EXCEPT ![p] = "waiting"]
      /\ loc' = [loc EXCEPT ![p] = "waiting"]
      /\ UNCHANGED <<turn>>
  \/ \E p \in {P1, P2}:
      /\ pc[p] = "waiting"
      /\ (p = turn)
      /\ pc' = [pc EXCEPT ![p] = "critical"]
      /\ loc' = [loc EXCEPT ![p] = "cs"]
      /\ UNCHANGED <<turn>>
  \/ \E p \in {P1, P2}:
      /\ pc[p] = "critical"
      /\ pc' = [pc EXCEPT ![p] = "non-critical"]
      /\ loc' = [loc EXCEPT ![p] = "non-critical"]
      /\ turn' = IF p = P1 THEN P2 ELSE P1

Spec == 
  WF_vars <<pc, loc>> /\
  Init /\ [][Next]_<<pc, loc>>

MutualExclusion == 
  \/ pc[P1] # "critical"
  \/ pc[P2] # "critical"
  \/ turn = P1
  \/ (loc[P1] # "cs" \/ loc[P2] # "cs")

LivenessP1 ==
  <>(pc[P1] = "critical")

Spec ==
  Spec /\ []MutualExclusion /\ LivenessP1

(*--algorithm mutual_exclusion_lock

variables turn \in {P1, P2};

process (p \in {P1, P2})
begin
non_critical:
  while TRUE do
    await pc[p] = "non-critical";
    pc[p] := "waiting";
    loc[p] := "waiting";
waiting:
    if p = turn then
      pc[p] := "critical";
      loc[p] := "cs";
critical:
      pc[p] := "non-critical";
      loc[p] := "non-critical";
      turn := (if p = P1 then P2 else P1);
    end if;
  end while;
end process;

end algorithm *)
```