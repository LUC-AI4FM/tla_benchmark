------------------------------- MODULE StonePuzzle -------------------------------

CONSTANTS W, N

VARIABLES partition

ASSUME W \in Nat /\ W > 0
ASSUME N \in Nat /\ N > 0

(*--algorithm StonePuzzle
variables partition = << >>;

next == \/ /\ Len(partition) < N
             /\ LET nextWeight = IF partition = << >> THEN 1 ELSE partition[Len(partition)] END
             IN CHOOSE w \in {w \in nextWeight..W - (N - Len(partition)) : 
                              \A i \in 1..Len(partition) : w >= partition[i] /\ w <= W - (N - Len(partition) + i - 1)} :
                /\ partition' = Append(partition, <<w>>)
           \/ /\ Len(partition) = N
              /\ SUM {partition[i] : i \in 1..Len(partition)} = W
              /\ \A weight \in 1..W : 
                 \E coeffs \in [1..N -> {-1, 0, 1}] :
                    SUM {coeffs[i] * partition[i] : i \in 1..N} = weight
           \/ /\ Len(partition) = N
              /\ NOT (\A weight \in 1..W : 
                        \E coeffs \in [1..N -> {-1, 0, 1}] :
                           SUM {coeffs[i] * partition[i] : i \in 1..N} = weight)
              /\ print("No solution")
           \/ /\ Len(partition) > N
              /\ partition' = << >>

begin
    while TRUE do
        await next;
        if Len(partition) = N then
            if \A weight \in 1..W : 
               \E coeffs \in [1..N -> {-1, 0, 1}] :
                  SUM {coeffs[i] * partition[i] : i \in 1..N} = weight
            then print(partition)
            else print("No solution")
        end if;
    od;
end algorithm;

=============================================================================