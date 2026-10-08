------------------------------- MODULE CigaretteSmokers -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS INGREDIENTS
ASSUME Cardinality(INGREDIENTS) >= 2

VARIABLES offer, smoking

Init == /\ offer \in SUBSET INGREDIENTS
        /\ Cardinality(offer) = Cardinality(INGREDIENTS) - 1
        /\ smoking \in INGREDIENTS \cup {<<>>}

Next ==
    \/ /\ offer \in SUBSET INGREDIENTS
       /\ Cardinality(offer) = Cardinality(INGREDIENTS) - 1
       /\ smoking = <<>>
       /\ \/ \E s \in INGREDIENTS : offer = INGREDIENTS \ {s}
          \/ offer = {}
    \/ /\ \E s \in INGREDIENTS : offer = INGREDIENTS \ {s} 
       /\ smoking = s

Spec ==
    /\ Init
    /\ [][Next]_<<offer, smoking>>
    /\ WF_next(<<offer, smoking>>)

TypeOK ==
    /\ offer \in SUBSET INGREDIENTS
    /\ Cardinality(offer) = Cardinality(INGREDIENTS) - 1
    /\ smoking \in INGREDIENTS \cup {<<>>}

Safety ==
    \/ smoking = <<>>
    \/ \A s1, s2 \in INGREDIENTS : s1 # s2 => (smoking = s1) \/ (smoking = s2)

Liveness ==
    \A s \in INGREDIENTS :
        \E offer' \in SUBSET INGREDIENTS :
            /\ Cardinality(offer') = Cardinality(INGREDIENTS) - 1
            /\ offer' = INGREDIENTS \ {s}
            /\ <>[]<>(smoking = s)

Progress ==
    <>[]<>(\E offer' \in SUBSET INGREDIENTS : Cardinality(offer') = Cardinality(INGREDIENTS) - 1)

WF_next(vars) == WF_vars(Next, vars)

=============================================================================