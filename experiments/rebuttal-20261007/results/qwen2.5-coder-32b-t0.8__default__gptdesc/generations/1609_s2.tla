---- MODULE Quicksort ----
EXTENDS Integers, Sequences, TLC

CONSTANTS ArrayLen

VARIABLES arr, pc, stack, left, right, pivot, i, j

(*--algorithm quicksort
variables arr = <<>>, pc = "Start", stack = <<>>, left = 0, right = ArrayLen - 1, pivot = 0, i = 0, j = 0;
begin
Start:
    if left < right then
        push: 
            stack := <<left, right>> \o stack;
            pc := "ChoosePivot";
    else
        pc := "PopOrDone";
end Start;

ChoosePivot:
    pivot := CHOOSE p \in {left .. right};
    i := left;
    j := right;
    pc := "Partition";

Partition:
    while i <= j do
        if arr[i] <= arr[pivot] then
            i := i + 1;
        else if arr[j] > arr[pivot] then
            j := j - 1;
        else
            swap: 
                arr := Swap(arr, i, j);
                i := i + 1;
                j := j - 1;
        end if;
    end while;
    pc := "SwapPivot";

SwapPivot:
    arr := Swap(arr, pivot, j);
    pc := "RecursiveCall";

RecursiveCall:
    if left < j - 1 then
        pushLeft: 
            stack := <<left, j - 1>> \o stack;
            pc := "ChoosePivot";
    else if j + 1 < right then
        pushRight: 
            stack := <<j + 1, right>> \o stack;
            pc := "ChoosePivot";
    else
        pc := "PopOrDone";
end RecursiveCall;

PopOrDone:
    if stack = <<>> then
        pc := "Done";
    else
        pop:
            <<left, right>> := Head(stack);
            stack := Tail(stack);
            pc := "ChoosePivot";
    end if;
end PopOrDone;

Done: skip;
end algorithm *)

Init == /\ arr \in [0 .. ArrayLen - 1 -> Int]
        /\ pc = "Start"
        /\ stack = <<>>
        /\ left = 0
        /\ right = ArrayLen - 1

Next == \/ /\ pc = "Start"
              /\ IF left < right THEN
                    /\ stack' = <<left, right>> \o stack
                    /\ pc' = "ChoosePivot"
                 ELSE
                    /\ pc' = "PopOrDone"
                 ENDIF
              /\ UNCHANGED <<arr, i, j, pivot>>
           \/ /\ pc = "ChoosePivot"
              /\ pivot' \in {left .. right}
              /\ i' = left
              /\ j' = right
              /\ pc' = "Partition"
              /\ UNCHANGED <<stack, arr>>
           \/ /\ pc = "Partition"
              /\ i <= j
              /\ IF arr[i] <= arr[pivot] THEN
                    /\ i' = i + 1
                    /\ UNCHANGED <<j, stack, arr, pivot>>
                 ELSE IF arr[j] > arr[pivot] THEN
                    /\ j' = j - 1
                    /\ UNCHANGED <<i, stack, arr, pivot>>
                 ELSE
                    /\ arr' = Swap(arr, i, j)
                    /\ i' = i + 1
                    /\ j' = j - 1
                    /\ UNCHANGED <<stack, pivot>>
                 ENDIF
              /\ pc' = "Partition"
           \/ /\ pc = "SwapPivot"
              /\ arr' = Swap(arr, pivot, j)
              /\ pc' = "RecursiveCall"
              /\ UNCHANGED <<i, j, stack, left, right, pivot>>
           \/ /\ pc = "RecursiveCall"
              /\ IF left < j - 1 THEN
                    /\ stack' = <<left, j - 1>> \o stack
                    /\ pc' = "ChoosePivot"
                 ELSE IF j + 1 < right THEN
                    /\ stack' = <<j + 1, right>> \o stack
                    /\ pc' = "ChoosePivot"
                 ELSE
                    /\ pc' = "PopOrDone"
                 ENDIF
              /\ UNCHANGED <<arr, i, j, pivot>>
           \/ /\ pc = "PopOrDone"
              /\ IF stack = <<>> THEN
                    /\ pc' = "Done"
                 ELSE
                    /\ <<left', right'>> = Head(stack)
                    /\ stack' = Tail(stack)
                    /\ pc' = "ChoosePivot"
                 ENDIF
              /\ UNCHANGED <<arr, i, j, pivot>>

Spec == Init /\ [][Next]_<<pc, arr, left, right, pivot, i, j, stack>> /\ WF_[Next]_<<pc, arr, left, right, pivot, i, j, stack>>
          /\ <>[](pc = "Done")

Swap(s, x, y) == s EXCEPT ![x] = s[y], ![y] = s[x]

Termination ==
    <>(/\ pc = "Done"
        /\ \E initArr \in [0 .. ArrayLen - 1 -> Int]:
            /\ arr = Permute(initArr)
            /\ \A k, l \in {0 .. ArrayLen - 1} : k <= l => initArr[k] <= initArr[l])

====