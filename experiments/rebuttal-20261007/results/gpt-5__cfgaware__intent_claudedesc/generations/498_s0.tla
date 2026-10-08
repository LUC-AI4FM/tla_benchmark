------------------------------ MODULE MultiInstanceConsensus ------------------------------

CONSTANTS
    Slots,
    Values

VARIABLES
    proposed, \* set of proposed values
    chosen    \* function from Slots to Values or "UNASSIGNED"

vars == << proposed, chosen >>

Init ==
    /\ proposed = {}
    /\ chosen = [ s \in Slots |-> "UNASSIGNED" ]

Propose ==
    /\ \E v \in (Values \ proposed):
          proposed' = proposed \cup {v}
    /\ chosen' = chosen

ChooseSlot(s) ==
    /\ s \in Slots
    /\ chosen[s] = "UNASSIGNED"
    /\ \E v \in proposed:
          chosen' = [chosen EXCEPT ![s] = v]
    /\ proposed' = proposed

Next ==
    Propose \/ \E s \in Slots: ChooseSlot(s)

TypeInvariant ==
    /\ proposed \subseteq Values
    /\ chosen \in [Slots -> (Values \cup {"UNASSIGNED"})]

Nontriviality ==
    []( \A s \in Slots: chosen[s] = "UNASSIGNED" \/ chosen[s] \in proposed )

Stability ==
    \A s \in Slots:
      \A v \in Values:
        []( (chosen[s] = v) => [](chosen[s] = v) )

Consistency ==
    [] ( \A s \in Slots:
           \A v1 \in Values:
             \A v2 \in Values:
               ( (chosen[s] = v1 /\ chosen[s] = v2) => v1 = v2 ) )

Liveness ==
    \A s \in Slots: <> (chosen[s] \in Values)

LiveSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Propose)
    /\ \A s \in Slots: WF_vars(ChooseSlot(s))

=============================================================================