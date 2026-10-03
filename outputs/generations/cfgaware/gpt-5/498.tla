------------------------------ MODULE MultiSlotConsensus ------------------------------

EXTENDS Naturals, TLC

(*
--algorithm MultiSlot
variables proposed = {}, chosen = [s \in Slots |-> {}];
fair process (P \in {0})
begin
Loop:
  either
    Propose:
      with v \in Values \ proposed do
        proposed := proposed \cup {v};
      end with;
  or
    Choose:
      with s \in Slots do
        if chosen[s] = {} then
          with v \in proposed do
            chosen[s] := {v};
          end with;
        end if;
      end with;
  end either;
  goto Loop;
end process;
end algorithm
*)

CONSTANTS Values, Slots

VARIABLES proposed, chosen, pc

vars == << proposed, chosen, pc >>

IsSingleton(S) == \E v: S = {v}

TypeOK ==
  /\ proposed \subseteq Values
  /\ chosen \in [Slots -> SUBSET Values]
  /\ \A s \in Slots: (chosen[s] = {}) \/ IsSingleton(chosen[s])

Nontriviality == \A s \in Slots: chosen[s] \subseteq proposed

PerSlotConsistency ==
  \A s \in Slots:
    \A v1, v2 \in Values: (v1 \in chosen[s] /\ v2 \in chosen[s]) => v1 = v2

ProcSet == {0}

Init ==
  /\ proposed = {}
  /\ chosen = [s \in Slots |-> {}]
  /\ pc = [i \in ProcSet |-> "Loop"]

Loop(i) ==
  /\ pc[i] = "Loop"
  /\ \/ /\ \E v \in Values \ proposed: TRUE
        /\ pc' = [pc EXCEPT ![i] = "Propose"]
     \/ /\ \E s \in Slots: chosen[s] = {}
        /\ proposed # {}
        /\ pc' = [pc EXCEPT ![i] = "Choose"]
  /\ UNCHANGED << proposed, chosen >>

Propose(i) ==
  /\ pc[i] = "Propose"
  /\ \E v \in Values \ proposed:
       /\ proposed' = proposed \cup {v}
       /\ chosen' = chosen
       /\ pc' = [pc EXCEPT ![i] = "Loop"]

Choose(i) ==
  /\ pc[i] = "Choose"
  /\ \E s \in Slots:
       /\ chosen[s] = {}
       /\ \E v \in proposed:
            /\ chosen' = [chosen EXCEPT ![s] = {v}]
            /\ proposed' = proposed
            /\ pc' = [pc EXCEPT ![i] = "Loop"]

Next == \E i \in ProcSet: Loop(i) \/ Propose(i) \/ Choose(i)

Spec == Init /\ [][Next]_vars

LiveSpec == Spec /\ WF_vars(Next)

StabilityAction == \A s \in Slots: chosen[s] # {} => chosen'[s] = chosen[s]

AllSlotsChosen == \A s \in Slots: chosen[s] # {}

THEOREM Spec => []TypeOK PROOF OMITTED
THEOREM Spec => []Nontriviality PROOF OMITTED
THEOREM Spec => []PerSlotConsistency PROOF OMITTED
THEOREM Spec => []StabilityAction PROOF OMITTED
THEOREM LiveSpec => <>AllSlotsChosen PROOF OMITTED

=============================================================================