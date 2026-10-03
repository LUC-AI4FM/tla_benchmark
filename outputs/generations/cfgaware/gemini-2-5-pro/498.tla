---- MODULE MultiSlotConsensus ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Slots, Values
ASSUME Slots # {}
ASSUME Values # {}

(*--algorithm MultiSlotConsensus
variables
    proposed = {};
    chosen = [s \in Slots |-> {}];

process P \in {1}
begin
MainLoop:
    while TRUE do
        either
            \* Propose a new value
            with v \in Values \setminus proposed do
                proposed := proposed \cup {v};
            end with;
        or
            \* Choose a value for an empty slot
            with s \in Slots, v \in proposed do
                if chosen[s] = {} then
                    chosen[s] := {v};
                end if;
            end with;
        end either;
    end while;
end process;
end algorithm*)
\* BEGIN TRANSLATION
VARIABLES proposed, chosen, pc

vars == <<proposed, chosen, pc>>

Init == (* Global variables *)
        /\ proposed = {}
        /\ chosen = [s \in Slots |-> {}]
        (* Process P *)
        /\ pc = [self \in {1} |-> "MainLoop"]

Propose == \E v \in Values \setminus proposed:
             /\ proposed' = proposed \cup {v}
             /\ UNCHANGED chosen

Choose == \E s \in Slots, v \in proposed:
            /\ chosen[s] = {}
            /\ chosen' = [chosen EXCEPT ![s] = {v}]
            /\ UNCHANGED proposed

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ \/ Propose
                     \/ Choose
                  /\ pc' = pc

Next == \E self \in {1}: MainLoop(self)

\* END TRANSLATION

\* Safety Properties

TypeOK == /\ proposed \in SUBSET Values
          /\ chosen \in [Slots -> SUBSET Values]

Nontriviality == \A s \in Slots: chosen[s] \subseteq proposed

PerSlotConsistency == \A s \in Slots: Cardinality(chosen[s]) <= 1

Stability == \A s \in Slots, v \in Values:
               (v \in chosen[s]) => \Box(v \in chosen[s])

\* Liveness Property

LiveSpec == \A s \in Slots: <> (chosen[s] # {})

=============================================================================