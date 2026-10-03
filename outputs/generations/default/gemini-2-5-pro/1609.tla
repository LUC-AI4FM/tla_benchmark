-------------------------- MODULE QuickSort --------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT ArrayLen, InitialArray

ASSUME  /\ ArrayLen \in 1..MaxInt
        /\ IsSeq(InitialArray)
        /\ Len(InitialArray) = ArrayLen
        /\ \A e \in DOMAIN InitialArray: InitialArray[e] \in Int

VARIABLES pc, stack, array

vars == <<pc, stack, array>>

(*--algorithm QuickSort
{
    variables array = InitialArray;

    procedure QS(low, high)
    variables pivot;
    {
        if low < high then
        QS_Choose_Pivot:
            with p \in low..high do
                pivot := p;
            end with;
        QS_Partition:
            with newArray \in { a \in Permutations(array) :
                                    /\ \A i \in 0..(ArrayLen-1): (i < low \/ i > high) => a[i] = array[i]
                                    /\ \A i \in low..pivot: \A j \in (pivot+1)..high : a[i] <= a[j] }
            do
                array := newArray;
            end with;
        QS_Recurse_Left:
            call QS(low, pivot);
        QS_Recurse_Right:
            call QS(pivot + 1, high);
        end if;
    }

    main {
    Start:
        call QS(0, ArrayLen - 1);
    Done:
        return;
    }
}
*)
\* BEGIN TRANSLATION
ProcSet == {"QS"}
Labels == {"Start", "Done", "QS_Entry", "QS_Choose_Pivot", "QS_Partition", "QS_Recurse_Left", "QS_Recurse_Right", "QS_Return"}

TypeOK ==   /\ pc \in Labels
            /\ array \in [0..ArrayLen-1 -> Int]
            /\ stack \in Seq(
                  [ low: Int, high: Int, pivot: Int, pc: Labels ]
               )

IsPermutation(s1, s2) == TLC!Bag(s1) = TLC!Bag(s2)

PreservesOutside(arr1, arr2, low, high) ==
    \A i \in (0..ArrayLen-1) \ (low..high) : arr1[i] = arr2[i]

IsPartitioned(arr, low, high, pivot) ==
    \A i \in low..pivot : \A j \in (pivot+1)..high : arr[i] <= arr[j]

IsSorted(arr) ==
    \A i \in 0..(Len(arr)-2) : arr[i] <= arr[i+1]

(* Main procedure call *)
Start ==    /\ pc = "Start"
            /\ pc' = "QS_Entry"
            /\ stack' = << [ low   |-> 0,
                             high  |-> ArrayLen - 1,
                             pivot |-> -1,  \* Placeholder, will be set in QS_Choose_Pivot
                             pc    |-> "Done" ] >>
            /\ array' = array

(* Procedure QS *)
QS_Entry == /\ pc = "QS_Entry"
            /\ LET frame == Head(stack) IN
                 IF frame.low < frame.high THEN
                   pc' = "QS_Choose_Pivot"
                 ELSE
                   pc' = "QS_Return"
            /\ UNCHANGED <<stack, array>>

QS_Choose_Pivot ==  /\ pc = "QS_Choose_Pivot"
                    /\ LET frame == Head(stack) IN
                        \E p \in frame.low..frame.high:
                           stack' = [ stack EXCEPT ![1].pivot = p ]
                    /\ pc' = "QS_Partition"
                    /\ UNCHANGED array

QS_Partition == /\ pc = "QS_Partition"
                /\ LET frame == Head(stack) IN
                     \E newArray:
                       /\ IsPermutation(array, newArray)
                       /\ PreservesOutside(array, newArray, frame.low, frame.high)
                       /\ IsPartitioned(newArray, frame.low, frame.high, frame.pivot)
                       /\ array' = newArray
                /\ pc' = "QS_Recurse_Left"
                /\ UNCHANGED stack

QS_Recurse_Left ==  /\ pc = "QS_Recurse_Left"
                    /\ LET frame == Head(stack) IN
                         LET new_frame == [ low   |-> frame.low,
                                            high  |-> frame.pivot,
                                            pivot |-> -1,
                                            pc    |-> "QS_Recurse_Right" ]
                         IN stack' = <<new_frame>> \o stack
                    /\ pc' = "QS_Entry"
                    /\ UNCHANGED array
                       
QS_Recurse_Right == /\ pc = "QS_Recurse_Right"
                    /\ LET frame == Head(stack) IN
                         LET new_frame == [ low   |-> frame.pivot + 1,
                                            high  |-> frame.high,
                                            pivot |-> -1,
                                            pc    |-> frame.pc ]
                         IN stack' = <<new_frame>> \o Tail(stack)
                    /\ pc' = "QS_Entry"
                    /\ UNCHANGED array

QS_Return ==    /\ pc = "QS_Return"
                /\ stack # <<>>
                /\ pc' = Head(stack).pc
                /\ stack' = Tail(stack)
                /\ UNCHANGED array

QS == QS_Entry \/ QS_Choose_Pivot \/ QS_Partition \/ QS_Recurse_Left \/ QS_Recurse_Right \/ QS_Return

(* Final state *)
Done == /\ pc = "Done"
        /\ UNCHANGED vars

Next == Start \/ QS \/ Done

Init == /\ pc = "Start"
        /\ stack = <<>>
        /\ array = InitialArray

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* END TRANSLATION

PermutationInvariant == IsPermutation(InitialArray, array)

Correctness == (pc = "Done") => (PermutationInvariant /\ IsSorted(array))

Termination == <>(pc = "Done")

THEOREM Spec => []PermutationInvariant /\ []Correctness /\ Termination
=============================================================================