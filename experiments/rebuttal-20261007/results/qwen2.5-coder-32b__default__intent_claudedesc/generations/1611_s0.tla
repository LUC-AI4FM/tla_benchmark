------------------------------- MODULE MergeSortSpec -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxLength

VARIABLES arr, temp, lo, hi, mid, i, j, k, state

(* --algorithm mergeSort
variables arr = <<>>, temp = <<>>, lo = 0, hi = 0, mid = 0, i = 0, j = 0, k = 0, state = "init";
begin
    while (state # "done") do
        if (state = "init") then
            with n \in {0 .. MaxLength} do
                arr := <<>>;
                temp := <<>>;
                lo := 0;
                hi := n - 1;
                state := "sort";
            endwith;
        else if (state = "sort" /\ lo < hi) then
            mid := (lo + hi) \div 2;
            state := "mergeSortLeft";
        else if (state = "mergeSortLeft") then
            i := lo;
            j := mid + 1;
            k := lo;
            state := "copyToTemp";
        else if (state = "copyToTemp" /\ k <= hi) then
            if (i > mid) then
                temp[k] := arr[j];
                j := j + 1;
            else if (j > hi) then
                temp[k] := arr[i];
                i := i + 1;
            else if (arr[i] < arr[j]) then
                temp[k] := arr[i];
                i := i + 1;
            else
                temp[k] := arr[j];
                j := j + 1;
            endif;
            k := k + 1;
        else if (state = "copyToTemp" /\ k > hi) then
            i := lo;
            while (i <= hi) do
                arr[i] := temp[i];
                i := i + 1;
            endwhile;
            state := "mergeSortRight";
        else if (state = "mergeSortRight") then
            state := "sort";
        else if (state = "sort" /\ lo >= hi) then
            state := "done";
        endif;
    endwhile;
end algorithm *)

Init == \/ state = "init"
        \/ \E n \in 0..MaxLength : arr = <<>> /\ temp = <<>> /\ lo = 0 /\ hi = n - 1 /\ mid = 0 /\ i = 0 /\ j = 0 /\ k = 0 /\ state = "sort"

Next == \/ (state = "init" /\ \E n \in 0..MaxLength : arr' = <<>> /\ temp' = <<>> /\ lo' = 0 /\ hi' = n - 1 /\ mid' = 0 /\ i' = 0 /\ j' = 0 /\ k' = 0 /\ state' = "sort")
        \/ (state = "sort" /\ lo < hi /\ mid' = (lo + hi) \div 2 /\ i' = lo /\ j' = mid' + 1 /\ k' = lo /\ state' = "mergeSortLeft")
        \/ (state = "mergeSortLeft" /\ i' = lo /\ j' = mid + 1 /\ k' = lo /\ state' = "copyToTemp")
        \/ (state = "copyToTemp" /\ k <= hi /\ 
            ((i > mid /\ temp'[k] = arr[j] /\ j' = j + 1 /\ i' = i)
             \/ (j > hi /\ temp'[k] = arr[i] /\ j' = j /\ i' = i + 1)
             \/ (arr[i] < arr[j] /\ temp'[k] = arr[i] /\ j' = j /\ i' = i + 1)
             \/ (temp'[k] = arr[j] /\ j' = j + 1 /\ i' = i))
            /\ k' = k + 1)
        \/ (state = "copyToTemp" /\ k > hi /\ i' = lo /\ state' = "mergeSortRight")
        \/ (state = "mergeSortRight" /\ state' = "sort")
        \/ (state = "sort" /\ lo >= hi /\ state' = "done")

Spec == Init /\ [][Next]_<<arr, temp, lo, hi, mid, i, j, k, state>> /\ WF_next(<<arr, temp, lo, hi, mid, i, j, k, state>>)

Sorted(seq) == \A x, y \in DOMAIN seq : x < y => seq[x] <= seq[y]

Termination == <>[](state = "done")

Invariant == Sorted(arr) \/ state # "done"

THEOREM Spec => []Invariant /\ Termination
=============================================================================