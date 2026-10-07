---- MODULE MultiSlotConsensus ----
EXTENDS FiniteSets

CONSTANTS
  Slots,   \* set of slot identifiers
  Values   \* set of values that may be proposed/chosen

ASSUME
  /\ Values # {}
  /\ IsFiniteSet(Values)
  /\ IsFiniteSet(Slots)

(*
--algorithm MultiSlotConsensus
variables
  Proposed = {},
  Chosen   = [s \in Slots |-> {}];

begin
Loop:
  while TRUE do
    either
Propose:
      with v \in Values \ Proposed do
        Proposed := Proposed \cup {v};
      end with;
    or
Choose:
      with s \in Slots do
        if (Chosen[s] = {}) /\ (Proposed # {}) then
          with v \in Proposed do
            Chosen[s] := {v};
          end with;
        end if;
      end with;
    end either;
  end while;
end algorithm
*)

(***************************************************************************)
(*                                   TLA+                                   *)
(***************************************************************************)

VARIABLES Proposed, Chosen

AtMostOne(S) ==
  S = {} \/ (\E v \in Values: S = {v})

Init ==
  /\ Proposed = {}
  /\ Chosen = [s \in Slots |-> {}]

ProposeNew ==
  \E v \in Values \ Proposed:
    /\ Proposed' = Proposed \cup {v}
    /\ Chosen' = Chosen

ChooseForSlot ==
  \E s \in Slots:
    /\ Chosen[s] = {}
    /\ Proposed # {}
    /\ \E v \in Proposed:
         /\ Chosen' = [Chosen EXCEPT ![s] = {v}]
         /\ Proposed' = Proposed

Next == ProposeNew \/ ChooseForSlot

Spec == Init /\ [][Next]_<Proposed, Chosen> /\ WF_<Proposed, Chosen>(Next)

(*
 Safety invariants
*)
TypeOK ==
  /\ Proposed \subseteq Values
  /\ Chosen \in [Slots -> SUBSET Values]
  /\ \A s \in Slots: AtMostOne(Chosen[s])

Nontriviality ==
  \A s \in Slots: Chosen[s] \subseteq Proposed

PerSlotConsistency ==
  \A s \in Slots: AtMostOne(Chosen[s])

(*
 Stability as an action-level safety property:
 in any step, once a slot is nonempty, it cannot be overwritten.
*)
NoOverwrite ==
  \A s \in Slots: (Chosen[s] # {}) => (Chosen'[s] = Chosen[s])

Stability ==
  [](NoOverwrite)

(*
 Liveness: under weak fairness of Next, eventually every slot is nonempty.
 The finiteness assumptions above ensure progress to a state with no empty slots.
*)
AllSlotsEventuallyNonempty ==
  <> (\A s \in Slots: Chosen[s] # {})

====