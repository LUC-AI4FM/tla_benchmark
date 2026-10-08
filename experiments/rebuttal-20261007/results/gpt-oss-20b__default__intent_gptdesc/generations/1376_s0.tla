------------------------------ MODULE GrowingRepository ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS Items

VARIABLE repo

Init ==
    /\ repo = {}

Add(item) ==
    /\ item ∈ Items
    /\ item ∉ repo
    /\ repo' = repo ∪ {item}

Next ==
    ∃ item ∈ Items : Add(item)

Spec ==
    Init /\ [][Next]_repo

SafetyInv ==
    repo ⊆ Items

EventualAddAll ==
    ∀ i ∈ Items : <> (i ∈ repo)

SomeAbsent ==
    ∃ i ∈ Items : [] ~(i ∈ repo)

AddAction ==
    ∃ item ∈ Items : Add(item)

FairnessCond == WF_vars(AddAction)
=============================================================================