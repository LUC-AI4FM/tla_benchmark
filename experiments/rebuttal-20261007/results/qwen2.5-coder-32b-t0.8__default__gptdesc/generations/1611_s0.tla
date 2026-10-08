------------------------------- MODULE MergeSortSpec -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS ArrayLen

VARIABLES pc, i, j, k, a, b, stack, low, high

(* --algorithm mergesort
variables a = <<>>, b = <<>>, stack = <<>>, pc = "Start", i = 0, j = 0, k = 0, low = 0, high = ArrayLen - 1;

while (low <= high) do
    if (high - low < 2) then
        if (a[low] > a[high]) then
            with (tmp == a[low]);
                a[low] := a[high];
                a[high] := tmp;
            end with;
        end if;
        pc := "Merge";
    else
        stack := <<low, high>> \o stack;
        high := low + ((high - low) DIV 2);
    end if;
end while;

while (stack # <<>>) do
    low := hd(stack);
    stack := tl(stack);
    high := hd(stack);
    stack := tl(stack);

    i := low;
    j := low + ((high - low) DIV 2) + 1;
    k := 0;

    while (i <= low + ((high - low) DIV 2)) \/ (j <= high) do
        if (i > low + ((high - low) DIV 2)) then
            b[k] := a[j];
            j := j + 1;
        else if (j > high) then
            b[k] := a[i];
            i := i + 1;
        else if (a[i] <= a[j]) then
            b[k] := a[i];
            i := i + 1;
        else
            b[k] := a[j];
            j := j + 1;
        end if;
        k := k + 1;
    end while;

    i := low;
    j := 0;

    while (i <= high) do
        a[i] := b[j];
        i := i + 1;
        j := j + 1;
    end while;

    pc := "Merge";
end while;

pc := "Done";
end algorithm *)

Init == /\ pc = "Start"
        /\ i = 0
        /\ j = 0
        /\ k = 0
        /\ low = 0
        /\ high = ArrayLen - 1
        /\ a \in SUBSEQ(1..ArrayLen)
        /\ b \in SUBSEQ(1..ArrayLen)
        /\ stack = <<>>

Next ==
    \/ /\ pc = "Start"
       /\ \/ /\ (high - low < 2)
              /\ \/ /\ a[low] > a[high]
                     /\ a' = [a EXCEPT ![low] = a[high], ![high] = a[low]]
                 \\/ /\ a' = a
              /\ pc' = "Merge"
          \\/ /\ high - low >= 2
              /\ stack' = <<low, high>> \o stack
              /\ high' = low + ((high - low) DIV 2)
              /\ /\ i' = i
                 /\ j' = j
                 /\ k' = k
                 /\ low' = low
                 /\ pc' = "Start"
    \/ /\ pc = "Merge"
       /\ stack # <<>>
       /\ low' = hd(stack)
       /\ stack' = tl(stack)
       /\ high' = hd(stack)
       /\ stack'' = tl(stack')
       /\ i' = low'
       /\ j' = low' + ((high' - low') DIV 2) + 1
       /\ k' = 0
       /\ pc' = "Merge"
    \/ /\ pc = "Merge"
       /\ stack = <<>>
       /\ pc' = "Done"

Sorted(seq) == \A i \in 1..Len(seq)-1 : seq[i] <= seq[i+1]

Spec ==
    /\ Init
    /\ [][Next]_<<pc, i, j, k, a, b, stack, low, high>>
    /\ WF_[Next]_<<pc, i, j, k, a, b, stack, low, high>>
    /\ <>(pc = "Done")
    /\ [](pc # "Done" => pc' = "Merge" \/ pc' = "Start")
    /\ [](pc = "Done" => Sorted(a))

=============================================================================