------------------------------ MODULE MultiSlotConsensus ------------------------------

EXTENDS TLC

CONSTANTS
  Slots,  \* Set of slot identifiers
  Values  \* Universe of values that can be proposed/chosen

(*
--algorithm MultiSlot
variables Proposed = {}, Chosen = [s \in Slots |-> {}];

fair process Daemon = "daemon"
begin
Loop:
  while TRUE do
    either
      \* Propose a new, previously unproposed value.
      with v \in Values \ Proposed do
        Proposed := Proposed \cup {v};
      end with;
    or
      \* Choose a proposed value for an empty slot.
      with s \in Slots do
        if Chosen[s] = {} then
          with v \in Proposed do
            Chosen[s] := {v};
          end with;
        end if;
      end with;
    end either;
  end while;
end process;

end algorithm
*)

VARIABLES
  Proposed,  \* Subset of Values that have been proposed.
  Chosen     \* Function from Slots to either {} or a singleton {v}.

vars == << Proposed, Chosen >>

IsSingleton(S) == \E v \in Values: S = {v}

Init ==
  /\ Proposed = {}
  /\ Chosen = [s \in Slots |-> {}]

ProposeNew ==
  \E v \in Values \ Proposed:
    /\ Proposed' = Proposed \cup {v}
    /\ UNCHANGED Chosen

ChooseForEmptySlot ==
  \E s \in Slots:
    /\ Chosen[s] = {}
    /\ \E v \in Proposed:
         /\ Chosen' = [Chosen EXCEPT ![s] = {v}]
         /\ UNCHANGED Proposed

Next == ProposeNew \/ ChooseForEmptySlot

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety (state) invariants
TypeOK ==
  /\ Proposed \subseteq Values
  /\ Chosen \in [Slots -> SUBSET Values]

Nontriviality ==
  \A s \in Slots: Chosen[s] \subseteq Proposed

PerSlotConsistency ==
  \A s \in Slots: (Chosen[s] = {}) \/ IsSingleton(Chosen[s])

\* Safety (action) properties
ProposalsMonotonic ==
  [] (Proposed \subseteq Proposed')

NeverUnchoose ==
  [] (\A s \in Slots: Chosen[s] \subseteq Chosen'[s])

\* Stability (never overwrite a chosen value)
Stability ==
  [] (\A s \in Slots: Chosen[s] # {} => Chosen'[s] = Chosen[s])

\* Liveness: under weak fairness of Next, every slot eventually becomes nonempty.
AllSlotsEventuallyNonEmpty ==
  \A s \in Slots: <> (Chosen[s] # {})

\* Optional theorems (proofs omitted)
THEOREM SafetyThm ==
  Spec => /\ []TypeOK
          /\ []Nontriviality
          /\ []PerSlotConsistency
          /\ ProposalsMonotonic
          /\ NeverUnchoose
          /\ Stability
PROOF OMITTED

THEOREM LivenessThm ==
  Spec => AllSlotsEventuallyNonEmpty
PROOF OMITTED

=============================================================================