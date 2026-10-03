---- MODULE MultiSlotConsensus ----

CONSTANTS Vals, Slots

(*
--algorithm MultiSlot
variables Proposed = {}, Chosen = [s \in Slots |-> {}];
begin
Loop:
  either
    with v \in Vals \ Proposed do
      Proposed := Proposed \cup {v};
    end with;
  or
    with s \in Slots, v \in Proposed do
      if Chosen[s] = {} then
        Chosen[s] := {v};
      end if;
    end with;
  end either;
  goto Loop;
end algorithm
*)

VARIABLES Proposed, Chosen

vars == << Proposed, Chosen >>

ASSUME Vals /= {} /\ Slots /= {}

Init ==
  /\ Proposed = {}
  /\ Chosen = [s \in Slots |-> {}]

Propose ==
  \E v \in Vals \ Proposed:
    /\ Proposed' = Proposed \cup {v}
    /\ Chosen' = Chosen

Pick ==
  \E s \in Slots:
    /\ Chosen[s] = {}
    /\ \E v \in Proposed:
         /\ Proposed' = Proposed
         /\ Chosen' = [Chosen EXCEPT ![s] = {v}]

Next == Propose \/ Pick

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*
Safety invariants
*)
TypeInv ==
  /\ Proposed \subseteq Vals
  /\ Chosen \in [Slots -> SUBSET Vals]

Nontriviality ==
  \A s \in Slots: Chosen[s] \subseteq Proposed

PerSlotConsistency ==
  \A s \in Slots:
    Chosen[s] = {} \/ (\E v \in Vals: Chosen[s] = {v})

(*
Stability: once a slot chooses a value, it never changes thereafter.
*)
StableSlot(s) == [](Chosen[s] /= {} => UNCHANGED Chosen[s])
Stability == \A s \in Slots: StableSlot(s)

THEOREM Spec => []TypeInv
THEOREM Spec => []Nontriviality
THEOREM Spec => []PerSlotConsistency
THEOREM Spec => Stability

(*
Liveness: under weak fairness of Next, eventually every slot becomes nonempty.
*)
AllChosenEventually == <>(\A s \in Slots: Chosen[s] /= {})
THEOREM Spec => AllChosenEventually

====