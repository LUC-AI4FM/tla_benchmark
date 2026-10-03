```tla
---- MODULE BalanceScale ----

CONSTANTS W, N

VARIABLES pieces

(*--algorithm BalanceScale
variables pieces = << >>;

fair process (P) = 1:
    while TRUE do
        with \E p \in Partitions(W, N): pieces' = p;
        if Balanced(pieces) then
            PrintT("Solution found: ", pieces);
            break;
        end if;
    end while;
end process;

(***************************************************************************
---- MODULE BalanceScale ----

CONSTANTS W, N

VARIABLES pieces

(*--algorithm BalanceScale
variables pieces = << >>;

fair process (P) = 1:
    while TRUE do
        with \E p \in Partitions(W, N): pieces' = p;
        if Balanced(pieces) then
            PrintT("Solution found: ", pieces);
            break;
        end if;
    end while;
end process;
***************************************************************************)

Partitions(w, n) == 
    IF n = 1 THEN { <<w>> }
    ELSE UNION {[p \o <<x>>] : p \in Partitions(w - x, n - 1), x \in 1..w}
    ENDIF

Balanced(pieces) ==
    /\ pieces \in [1..W -> {-1, 0, 1}]
    /\ \A t \in 1..W: \E coeffs \in [pieces -> {-1, 0, 1}]: 
        Sum(coeffs) = t

Sum(coeffs) == 
    LET weightedPieces == {coeffs[p] * p : p \in DOMAIN coeffs}
    IN  \o +/ weightedPieces

ASSUME CHOOSE pieces: Balanced(pieces)

end algorithm;
----*)

end module
```

Note: The provided specification includes a recursive operator `Partitions` to generate all possible ordered partitions of weight `W` into `N` natural-number weights. It also defines an operator `Balanced` that checks if the given sequence of pieces can balance every target weight from 1 to W using coefficients in {-1, 0, 1}. The `Sum` operator calculates the weighted sum of a sequence of pieces with given coefficients.

The algorithm process attempts to find a valid partition and prints it if found. The `ASSUME` statement is used to search for a solution that satisfies the `Balanced` condition. 

Please ensure that the constants `W` and `N` are defined in your TLC configuration file, as they are not assigned values within this specification.