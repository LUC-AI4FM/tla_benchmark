---- MODULE TlaToPcalMapping ----

EXTENDS Sequences, FiniteSets, TLC

CONSTANTS 
    Locations,  \* A set of all possible locations (e.g., line numbers)
    Tokens      \* A set of all possible tokens (e.g., keywords, identifiers)

VARIABLES 
    regions,    \* A sequence of region objects
    tpObjects   \* A sequence of translation objects

\* A region is defined by a start and end location
Region == [start \in Locations, end \in Locations]

\* A TPObject represents a mapping from TLA+ to PlusCal code regions
TPObject == [tlaRegion \in Region, pcalRegion \in Region]

Init ==
    /\ regions = << >>
    /\ tpObjects = << >>

Next ==
    \/ /\ E r \in Region : regions' = Append(regions, <<r>>)
       /\ UNCHANGED tpObjects
    \/ /\ E tpo \in TPObject : tpObjects' = Append(tpObjects, <<tpo>>)
       /\ UNCHANGED regions

\* Invariants for well-formedness and ordering of regions and tpObjects
Spec ==
    /\ Init
    /\ [][Next]_<<regions, tpObjects>>
    /\ Stable({regions} \cup {tpObjects})
    /\ \A r1, r2 \in regions : r1.start < r2.start => r1.end <= r2.start
    /\ \A tpo1, tpo2 \in tpObjects : tpo1.tlaRegion.start < tpo2.tlaRegion.start => tpo1.tlaRegion.end <= tpo2.tlaRegion.start

END MODULE
========================================