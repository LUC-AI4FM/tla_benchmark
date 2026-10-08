------------------------------- MODULE MergeSortSpec -------------------------------

CONSTANTS MaxArrayLen

VARIABLES array, tempArray, lo, hi, auxLo, auxHi, i, j, k

(*--algorithm MergeSort
variables array = <<>>, tempArray = <<>>, lo = 0, hi = -1, auxLo = 0, auxHi = -1, i = 0, j = 0, k = 0;

fair process (Init)
begin
    with n \in 0..MaxArrayLen do
        array := <<>>;
        tempArray := <<>>;
        lo := 0;
        hi := n - 1;
        while i < n do
            array := Append(array, CHOOSE x \in 0..MaxArrayLen : TRUE);
            i := i + 1;
        end while;
    end with;
end process;

fair process (Sort)
begin
    while lo <= hi do
        auxLo := lo;
        auxHi := hi;
        await hi - lo >= 1;
        mid \in lo..hi \div 2;
        Sort!lo := auxLo; Sort!hi := mid;
        || Sort!lo := mid + 1; Sort!hi := auxHi;
        Merge(auxLo, mid, auxHi);
    end while;
end process;

fair process (Merge)
variables i = auxLo, j = mid + 1, k = auxLo
begin
    while k <= auxHi do
        if i > mid then
            tempArray[k] := array[j];
            j := j + 1;
        else if j > auxHi then
            tempArray[k] := array[i];
            i := i + 1;
        else if array[i] <= array[j] then
            tempArray[k] := array[i];
            i := i + 1;
        else
            tempArray[k] := array[j];
            j := j + 1;
        end if;
        k := k + 1;
    end while;
    i \in auxLo..auxHi;
    while i <= auxHi do
        array[i] := tempArray[i];
        i := i + 1;
    end while;
end process;

end algorithm;*)

Spec == Init /\ [][Sort \/ Merge]_<<array, tempArray, lo, hi, auxLo, auxHi, i, j, k>>

Termination == <<array, tempArray, lo, hi, auxLo, auxHi, i, j, k>> \in StateSpace /\ lo > hi

defaultInitValue == 0

ArrayLen == Len(array)

Invariant ==
    /\ ArrayLen <= MaxArrayLen
    /\ \/ lo > hi
       \/ \A x, y \in DOMAIN array : x < y => array[x] <= array[y]

=============================================================================