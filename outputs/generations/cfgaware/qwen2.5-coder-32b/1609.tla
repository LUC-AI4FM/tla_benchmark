------------------------------- MODULE QuickSort -------------------------------

CONSTANTS ArrayLen

VARIABLES pc, stack, arr, lo, hi

(*--algorithm Quicksort
variables arr = [1..ArrayLen -> ?], lo = 1, hi = ArrayLen;
procedure QS(lo, hi)
    variables pivot, i, j, temp;
begin
    if (lo < hi) then
        pivot := arr[Choose({lo .. hi})];
        i := lo - 1;
        j := hi + 1;
        while TRUE do
            i := i + 1;
            while arr[i] < pivot do
                i := i + 1;
            end while;
            j := j - 1;
            while arr[j] > pivot do
                j := j - 1;
            end while;
            if (i >= j) then
                break;
            else
                temp := arr[i];
                arr[i] := arr[j];
                arr[j] := temp;
            end if;
        end while;
        if (lo < j) then
            call QS(lo, j);
        end if;
        if (j + 1 < hi) then
            call QS(j + 1, hi);
        end if;
    end if;
end procedure;

begin
    call QS(lo, hi);
    print arr;
end algorithm *)

Init == /\ pc = "QS"
        /\ stack = << >>
        /\ lo = 1
        /\ hi = ArrayLen
        /\ arr \in [1..ArrayLen -> Nat]

Next ==
    \/ /\ pc = "QS"
       /\ (lo >= hi)
       /\ stack # << >>
       /\ LET frame == Head(stack) IN
          /\ UNCHANGED <<arr, lo>>
          /\ hi' = frame.hi
          /\ lo' = frame.lo
          /\ pc' = "Return"
          /\ stack' = Tail(stack)
    \/ /\ pc = "QS"
       /\ (lo < hi)
       /\ LET pivot \in {lo .. hi} IN
          /\ LET i \in 1..ArrayLen, j \in 1..ArrayLen BE
             /\ /\ i >= lo - 1
                /\ j <= hi + 1
                /\ \/ /\ i' = i + 1
                       /\ arr[i'] < pivot
                       /\ j' = j
                   \/ /\ i' = i
                      /\ j' = j - 1
                      /\ arr[j'] > pivot
                   \/ /\ i >= j
                      /\ pc' = "PartitionDone"
                      /\ lo' = lo
                      /\ hi' = hi
                      /\ stack' = stack
                      /\ arr' \in Permutations(arr)
                      /\ (\A k \in 1..lo-1 : arr'[k] = arr[k])
                      /\ (\A k \in hi+1..ArrayLen : arr'[k] = arr[k])
                      /\ (\A k \in lo..j : arr'[k] <= pivot)
                      /\ (\A k \in j+1..hi : arr'[k] >= pivot)
    \/ /\ pc = "PartitionDone"
       /\ LET pivot \in {lo .. hi} IN
          /\ LET i \in 1..ArrayLen, j \in 1..ArrayLen BE
             /\ /\ i >= lo - 1
                /\ j <= hi + 1
                /\ i >= j
                /\ \/ /\ (lo < j)
                       /\ pc' = "QS"
                       /\ lo' = lo
                       /\ hi' = j
                       /\ stack' = <<[lo |-> lo, hi |-> hi]>> \o stack
                   \/ /\ (j + 1 < hi)
                      /\ pc' = "QS"
                      /\ lo' = j + 1
                      /\ hi' = hi
                      /\ stack' = <<[lo |-> lo, hi |-> hi]>> \o stack
    \/ /\ pc = "Return"
       /\ LET frame == Head(stack) IN
          /\ UNCHANGED <<arr, lo>>
          /\ hi' = frame.hi
          /\ lo' = frame.lo
          /\ pc' = "QS"
          /\ stack' = Tail(stack)

Spec ==
    /\ Init
    /\ [][Next]_<<pc, stack, arr, lo, hi>>
    /\ WF_[Next]_<<pc, stack, arr, lo, hi>>

Termination ==
    <>(pc = "Done")

Sorted(subarray) == \A i \in 1..Len(subarray)-1 : subarray[i] <= subarray[i+1]

Permutations(S) == {f \in [S -> S] : (\A v \in S : Cardinality({k \in DOMAIN f : f[k] = v}) = Cardinality({k \in DOMAIN S : S[k] = v}))}

=============================================================================