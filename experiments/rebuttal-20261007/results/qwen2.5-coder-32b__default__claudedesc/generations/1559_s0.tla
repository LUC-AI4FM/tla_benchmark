------------------------------- MODULE LockHS -------------------------------

EXTENDS Lock, Stuttering

CONSTANTS N \* Number of processes

VARIABLES pc, turn, h_turn, s

InitHS == Init /\ h_turn = 1 /\ s = top

l1HS ==
    \/ /\ s = top
       /\ s' = stutter_0
       /\ UNCHANGED <<pc, turn, h_turn>>
    \/ /\ s = stutter_0
       /\ s' = stutter_1
       /\ UNCHANGED <<pc, turn, h_turn>>
    \/ /\ s = stutter_1
       /\ l1
       /\ IF pc[proposing] = "entry" THEN h_turn' = proposing ELSE h_turn' = h_turn

SpecHS ==
    InitHS /\ [][Next \/ l1HS \/ l0 \/ cs \/ l2]_<<pc, turn, h_turn, s>>

TypeOKHS ==
    /\ TYPEOK
    /\ h_turn \in 1..N
    /\ s \in {top} \cup {stutter_0} \cup {stutter_1}

InvHS ==
    /\ (s = top => pc[proposing] # "entry" \/ h_turn = proposing)
    /\ (s = stutter_0 => pc[proposing] = "entry")
    /\ (s = stutter_1 => pc[proposing] = "entry")

pc_translation ==
    [p \in 1..N |-> IF s = top THEN pc[p]
                      ELSE IF s = stutter_0 THEN "entry"
                      ELSE IF s = stutter_1 THEN "entry"
                      ELSE "exit"]

c_translation ==
    [p \in 1..N |-> IF s = top THEN c[p]
                      ELSE FALSE]

Spec == SpecHS /\ TypeOKHS /\ InvHS /\ LockInv

P == Peterson(N)

PSpec ==
    P!Init /\ [][P!Next]_<<P!pc, P!turn>>

THEOREM Spec => PSpec
THEOREM PSpec => Spec

=============================================================================