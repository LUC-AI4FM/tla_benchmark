------------------------------- MODULE QuickSortSpec -------------------------------

CONSTANTS ArrayLen

VARIABLES array, stack

(*--algorithm QuickSort
variables array = [i \in 1..ArrayLen -> CHOOSE x \in 1..ArrayLen: TRUE],
          stack = <<1, ArrayLen>>;

fair process (P) = 1:
    while stack # <> do
        with lo = FIRST(stack),
             hi = SECOND(stack)
        do
            if lo < hi then
                let pivotIndex \in lo..hi be undefined,
                    partitionedArray \in Permutations(array) :
                        /\ \A i \in lo..pivotIndex-1: array[i] <= array[pivotIndex]
                        /\ \A i \in pivotIndex+1..hi: array[pivotIndex] <= array[i]
                in
                    array' = [array EXCEPT ![i \in 1..ArrayLen] = partitionedArray[i]],
                    stack' = <<lo, pivotIndex-1>> \o <<pivotIndex+1, hi>> \o (stack \ {<<lo, hi>>})
            else
                skip;
        end if;
    end while;
end process;

end algorithm;*)

Spec == /\ Init
        /\ \A s \in States: Action(s) => Inv(s)

Init ==
    /\ array = [i \in 1..ArrayLen -> CHOOSE x \in 1..ArrayLen: TRUE]
    /\ stack = <<1, ArrayLen>>

Inv ==
    /\ array \in [1..ArrayLen -> 1..ArrayLen]
    /\ stack \subseteq SUBSET (1..ArrayLen) \X (1..ArrayLen)
    /\ \A s \in stack: FIRST(s) <= SECOND(s)

Action ==
    \/ /\ stack # <<>>
       /\ LET lo == FIRST(stack),
              hi == SECOND(stack)
          IN
             /\ lo < hi
             /\ \E pivotIndex \in lo..hi, partitionedArray \in Permutations(array):
                    /\ \A i \in lo..pivotIndex-1: array[i] <= array[pivotIndex]
                    /\ \A i \in pivotIndex+1..hi: array[pivotIndex] <= array[i]
                    /\ array' = [array EXCEPT ![i \in 1..ArrayLen] = partitionedArray[i]]
                    /\ stack' = <<lo, pivotIndex-1>> \o <<pivotIndex+1, hi>> \o (stack \ {<<lo, hi>>})
       \/ /\ stack # <<>>
          /\ LET lo == FIRST(stack),
                 hi == SECOND(stack)
             IN
                /\ lo >= hi
                /\ array' = array
                /\ stack' = stack \ {<<lo, hi>>}
       \/ stack = <<>>

Termination ==
    []<> (stack = <>)

=============================================================================