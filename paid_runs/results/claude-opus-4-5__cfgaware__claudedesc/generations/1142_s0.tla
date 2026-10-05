---------------------------- MODULE TPSpec ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT TPSpec, tpRegion

\* Basic type definitions
Location == [line : Nat, column : Nat]

\* A region is a pair of locations where begin <= end (lexicographically)
Region == {r \in [begin : Location, end : Location] : 
            \/ r.begin.line < r.end.line
            \/ (r.begin.line = r.end.line /\ r.begin.column <= r.end.column)}

\* TPObject types
TLAToken == [type : {"TLAToken"}, region : Region, pcalRegion : Region]
Paren == [type : {"Paren"}, loc : Location, pcalLoc : Location, kind : {"left", "right"}]
Break == [type : {"Break"}, depth : Nat]

TPObject == TLAToken \cup Paren \cup Break

\* Check if a location is before or equal to another
LocLEQ(loc1, loc2) == 
    \/ loc1.line < loc2.line
    \/ (loc1.line = loc2.line /\ loc1.column <= loc2.column)

LocLT(loc1, loc2) ==
    \/ loc1.line < loc2.line
    \/ (loc1.line = loc2.line /\ loc1.column < loc2.column)

\* Check if a TPObject is a token
IsToken(obj) == obj.type = "TLAToken"

\* Check if a TPObject is a left paren
IsLeftParen(obj) == obj.type = "Paren" /\ obj.kind = "left"

\* Check if a TPObject is a right paren
IsRightParen(obj) == obj.type = "Paren" /\ obj.kind = "right"

\* Check if a TPObject is a break
IsBreak(obj) == obj.type = "Break"

\* Get the location/region of a TPObject for ordering
ObjLoc(obj) == 
    IF obj.type = "TLAToken" THEN obj.region.begin
    ELSE IF obj.type = "Paren" THEN obj.loc
    ELSE [line |-> 0, column |-> 0]

\* Check if sequence is a valid TPSpec
IsValidTPSpec(spec) ==
    /\ spec \in Seq(TPObject)
    /\ \A i \in 1..Len(spec) : 
        \A j \in (i+1)..Len(spec) :
            (IsToken(spec[i]) /\ IsToken(spec[j])) => 
                LocLEQ(spec[i].region.end, spec[j].region.begin)
    /\ \A i \in 1..Len(spec) :
        IsBreak(spec[i]) => 
            /\ i > 1 /\ i < Len(spec)
            /\ IsRightParen(spec[i-1])
            /\ IsLeftParen(spec[i+1])

\* Compute parenthesis depth at position i
ParenDepth(spec, i) ==
    LET CountParens(j) == 
        IF j < 1 \/ j > Len(spec) THEN 0
        ELSE IF IsLeftParen(spec[j]) THEN 1
        ELSE IF IsRightParen(spec[j]) THEN -1
        ELSE 0
    IN IF i < 1 THEN 0
       ELSE IF i = 1 THEN CountParens(1)
       ELSE ParenDepth(spec, i-1) + CountParens(i)

\* Find token positions that best cover a region
RegionToTokPair(spec, reg) ==
    LET TokenPositions == {i \in 1..Len(spec) : IsToken(spec[i])}
        
        \* Find leftmost token that overlaps or follows region begin
        LeftCandidates == {i \in TokenPositions : 
            \/ LocLEQ(spec[i].region.begin, reg.begin)
            \/ LocLEQ(reg.begin, spec[i].region.end)}
        
        RightCandidates == {i \in TokenPositions :
            \/ LocLEQ(reg.end, spec[i].region.end)
            \/ LocLEQ(spec[i].region.begin, reg.end)}
        
        LeftPos == IF LeftCandidates = {} THEN 
                      IF TokenPositions = {} THEN 0
                      ELSE CHOOSE i \in TokenPositions : 
                           \A j \in TokenPositions : i <= j
                   ELSE CHOOSE i \in LeftCandidates :
                        \A j \in LeftCandidates : i <= j
                        
        RightPos == IF RightCandidates = {} THEN
                       IF TokenPositions = {} THEN 0
                       ELSE CHOOSE i \in TokenPositions :
                            \A j \in TokenPositions : j <= i
                    ELSE CHOOSE i \in RightCandidates :
                         \A j \in RightCandidates : j <= i
    IN <<LeftPos, RightPos>>

\* Variables for the algorithm
VARIABLES pc, i, left, right, rtokDepth, minDepth

vars == <<pc, i, left, right, rtokDepth, minDepth>>

\* Initial state
Init == 
    /\ pc = "Lbl_1"
    /\ i = 0
    /\ left = 0
    /\ right = 0
    /\ rtokDepth = 0
    /\ minDepth = 0

\* First label: compute token pair
Lbl_1 == 
    /\ pc = "Lbl_1"
    /\ LET tokPair == RegionToTokPair(TPSpec, tpRegion)
       IN /\ left' = tokPair[1]
          /\ right' = tokPair[2]
          /\ i' = tokPair[1]
          /\ rtokDepth' = 0
          /\ minDepth' = 0
    /\ pc' = "Lbl_2"

\* Second label: iterate and compute depths
Lbl_2 ==
    /\ pc = "Lbl_2"
    /\ IF i <= right /\ i >= 1 /\ i <= Len(TPSpec)
       THEN 
            LET depthChange == 
                IF IsLeftParen(TPSpec[i]) THEN 1
                ELSE IF IsRightParen(TPSpec[i]) THEN -1
                ELSE 0
                newDepth == rtokDepth + depthChange
            IN /\ rtokDepth' = newDepth
               /\ minDepth' = IF newDepth < minDepth THEN newDepth ELSE minDepth
               /\ i' = i + 1
               /\ pc' = "Lbl_2"
               /\ UNCHANGED <<left, right>>
       ELSE
            /\ pc' = "Done"
            /\ UNCHANGED <<i, left, right, rtokDepth, minDepth>>

\* Termination state
Done == 
    /\ pc = "Done"
    /\ UNCHANGED vars

\* Next state relation
Next == Lbl_1 \/ Lbl_2 \/ Done

\* Temporal specification
Spec == Init /\ [][Next]_vars

\* Termination property
Termination == <>(pc = "Done")

\* Type invariant
TypeOK ==
    /\ pc \in {"Lbl_1", "Lbl_2", "Done"}
    /\ i \in Nat
    /\ left \in Nat
    /\ right \in Nat
    /\ rtokDepth \in Int
    /\ minDepth \in Int

=======================================================================