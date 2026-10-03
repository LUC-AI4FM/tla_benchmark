-------------------------- MODULE PcalTlaMapping --------------------------
EXTENDS Integers, Sequences, FiniteSets, Records, TLC, Strings

CONSTANTS
    AllTokens,      \* A sequence of all tokens in the source code.
    InputTlaRegion  \* The TLA+ region to analyze.

\* A location is a line and column pair.
Location(line, col) == [line |-> line, column |-> col]

\* A region is a start and end location.
Region(startLoc, endLoc) == [start |-> startLoc, end |-> endLoc]

\* A token is a value and a region.
Token(val, reg) == [value |-> val, region |-> reg]

\* Lexicographical ordering for locations.
LocationLE(loc1, loc2) ==
    (loc1.line < loc2.line) \/ (loc1.line = loc2.line /\ loc1.column <= loc2.column)

\* A region is well-formed if its start is not after its end.
WellFormedRegion(reg) ==
    /\ reg \in [start: [line: Int, column: Int], end: [line: Int, column: Int]]
    /\ LocationLE(reg.start, reg.end)

\* Checks if the inner region is contained within the outer region.
RegionContains(outer, inner) ==
    /\ WellFormedRegion(outer)
    /\ WellFormedRegion(inner)
    /\ LocationLE(outer.start, inner.start)
    /\ LocationLE(inner.end, outer.end)

\* Type predicate for a sequence of tokens.
IsSequenceOfTokens(seq) ==
    /\ \A i \in DOMAIN seq :
        /\ seq[i] \in [value: STRING, region: [start: [line: Int, column: Int],
                                              end: [line: Int, column: Int]]]
        /\ WellFormedRegion(seq[i].region)

\* Checks if a sequence of tokens is sorted by their start location.
IsSorted(seq) ==
    \A i \in 1..(Len(seq) - 1) : LocationLE(seq[i].region.start, seq[i+1].region.start)

ASSUME IsSequenceOfTokens(AllTokens)
ASSUME IsSorted(AllTokens)
ASSUME WellFormedRegion(InputTlaRegion)

(***************************************************************************)
(* The following specification is a TLA+ translation of a PlusCal          *)
(* algorithm that analyzes tokens within a given TLA+ region.              *)
(***************************************************************************)
VARIABLES pc, tokens_in_region, paren_depth, max_paren_depth, i, sorted_tokens

vars == <<pc, tokens_in_region, paren_depth, max_paren_depth, i, sorted_tokens>>

TypeOK ==
    /\ pc \in {"FindTokens", "AnalyzeTokens", "FinalCheck", "Done"}
    /\ IsSequenceOfTokens(tokens_in_region)
    /\ paren_depth \in Int
    /\ max_paren_depth \in Int
    /\ i \in Int
    /\ IsSequenceOfTokens(sorted_tokens)

Init ==
    /\ pc = "FindTokens"
    /\ tokens_in_region = << >>
    /\ paren_depth = 0
    /\ max_paren_depth = 0
    /\ i = 1
    /\ sorted_tokens = << >>

FindTokens ==
    /\ pc = "FindTokens"
    /\ LET selected == SelectSeq(AllTokens, LAMBDA t: RegionContains(InputTlaRegion, t.region))
       IN /\ sorted_tokens' = selected
          /\ Assert(IsSorted(selected), "Failure: Selected tokens are not sorted.")
          /\ tokens_in_region' = selected
    /\ pc' = "AnalyzeTokens"
    /\ UNCHANGED <<paren_depth, max_paren_depth, i>>

AnalyzeTokens ==
    /\ pc = "AnalyzeTokens"
    /\ IF i <= Len(tokens_in_region)
       THEN /\ LET token == tokens_in_region[i]
               IN LET new_paren_depth ==
                        IF token.value = "(" THEN paren_depth + 1
                        ELSE IF token.value = ")" THEN paren_depth - 1
                        ELSE paren_depth
                  IN /\ Assert(token.value # ")" \/ paren_depth > 0, "Failure: Unmatched closing parenthesis.")
                     /\ paren_depth' = new_paren_depth
                     /\ max_paren_depth' = IF new_paren_depth > max_paren_depth
                                           THEN new_paren_depth
                                           ELSE max_paren_depth
            /\ i' = i + 1
            /\ pc' = "AnalyzeTokens"
       ELSE /\ pc' = "FinalCheck"
            /\ UNCHANGED <<paren_depth, max_paren_depth, i>>
    /\ UNCHANGED <<tokens_in_region, sorted_tokens>>

FinalCheck ==
    /\ pc = "FinalCheck"
    /\ Assert(paren_depth = 0, "Failure: Unmatched opening parenthesis at the end.")
    /\ pc' = "Done"
    /\ UNCHANGED <<tokens_in_region, paren_depth, max_paren_depth, i, sorted_tokens>>

Next == FindTokens \/ AnalyzeTokens \/ FinalCheck
           \/ (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

=============================================================================