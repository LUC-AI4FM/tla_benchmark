MODULE RegionMapping
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS TEXT, REGION_SET

VARIABLES tokens, translations

(* -------------------------------------------------------------------- *)
\* Type definition for a region (start and end positions in the token sequence)
Region == [start: Nat, end: Nat]

(* -------------------------------------------------------------------- *)
\* Predicate that checks whether a region lies within the bounds of the
\* current token sequence.
IsWithinBounds(r) ==
    r.start <= r.end /\ r.start >= 1 /\ r.end <= Len(tokens)

WellFormedRegion(r) == IsWithinBounds(r)

(* -------------------------------------------------------------------- *)
\* Helper that produces an ordered list from a set of indices.
SortedIndices(inds) ==
    [i \in 1..Len(tokens) : i ∈ inds]   (* preserves increasing order *)

TokenSeqByIndices(inds) ==
    [tokens[i] | i \in inds]

(* -------------------------------------------------------------------- *)
\* Recursive predicate that checks whether a sequence of tokens has
\* balanced parentheses.
BalancedParen(seq) ==
    LET
      helper(i,d) == IF i > Len(seq) THEN d = 0
                    ELSE IF seq[i] = "(" THEN helper(i+1, d+1)
                         ELSE IF seq[i] = ")" THEN (d>0) /\ helper(i+1, d-1)
                         ELSE helper(i+1, d)
    IN helper(1,0)

BalancedParenByIndices(inds) ==
    BalancedParen(TokenSeqByIndices(SortedIndices(inds)))

(* -------------------------------------------------------------------- *)
\* Compute the list of token indices that belong to a region.
ComputeMapping(r) ==
    SortedIndices({i \in 1..Len(tokens) : r.start <= i /\ i <= r.end})

(* -------------------------------------------------------------------- *)
\* Initial state: the token sequence is the supplied TEXT constant and
\* no translations have been computed yet.
Init ==
    /\ tokens = TEXT
    /\ translations = [r \in REGION_SET |-> << >>]

(* -------------------------------------------------------------------- *)
\* Next-state relation.  In each step one region gets its mapping
\* computed.  All other regions keep their current mappings unchanged.
Next ==
    ∃ r \in REGION_SET :
        LET newTrans == [translations EXCEPT ![r] = ComputeMapping(r)]
        IN translations' = newTrans

(* -------------------------------------------------------------------- *)
\* Safety invariants that must hold in every reachable state.
WFRegions ==
    ∀ r ∈ REGION_SET : WellFormedRegion(r)

TokenOrderingInv ==
    ∀ r ∈ REGION_SET :
        ∀ i ∈ 1..Len(translations[r]) - 1 :
            translations[r][i] < translations[r][i+1]

BalancedParenthesesInv ==
    ∀ r ∈ REGION_SET : BalancedParenByIndices(translations[r])

Safety == WFRegions /\ TokenOrderingInv /\ BalancedParenthesesInv

(* -------------------------------------------------------------------- *)
\* Liveness property: eventually every region will have a non‑empty mapping.
AllMapped ==
   ∀ r \in REGION_SET : translations[r] # << >>

Liveness == <> AllMapped

(* -------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<tokens, translations>>

END MODULE