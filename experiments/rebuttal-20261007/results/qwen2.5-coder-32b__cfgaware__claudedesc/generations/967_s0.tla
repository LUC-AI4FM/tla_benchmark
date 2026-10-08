---- MODULE CarTalkPuzzle ----

CONSTANTS W, N

VARIABLES \* No variables defined in this specification

(*--algorithm CarTalkPuzzle
variables seq;

begin
    with validPartition \in Partitions(<<>>, W) do
        if \A wt \in 1..W : Weighs(validPartition, wt) then
            PrintT("Solution found: " <> ToString(validPartition));
            skip;
        else
            PrintT("No solution");
        end if;
    end with;
end algorithm;*)

Partitions(seq, wt) == 
    IF Len(seq) = N THEN
        IF wt = 0 THEN {seq} ELSE {} ENDIF
    ELSE
        LET min \in (IF seq = <<>> THEN 1 ELSE seq[Len(seq)] ENDIF)
            max \in (W - (N - Len(seq)) * min)
        IN  UNION {Partitions(Append(seq, x), wt - x) : x \in min..max}
    ENDIF

Weighs(seq, wt) ==
    LET coeffs == {-1, 0, 1}
    IN  \E assignment \in [seq -> coeffs] :
            \Sum{i \in DOMAIN seq} (assignment[i] * seq[i]) = wt

ASSUME CHOOSE validPartition \in Partitions(<<>>, W) :
    \A wt \in 1..W : Weighs(validPartition, wt)

====