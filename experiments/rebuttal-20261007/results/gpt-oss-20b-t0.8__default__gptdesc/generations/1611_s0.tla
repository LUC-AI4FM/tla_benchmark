----------------------------- MODULE MergeSortSpec -----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS MaxLen, MaxVal

VARIABLES arr, b, stack, len

(* Frame predicates *)
StartF(f) == f.phase = "start"
LeftF(f)  == f.phase = "left"
RightF(f) == f.phase = "right"
MergeF(f) == f.phase = "merge"

(* Invariant that the array is sorted when sorting is finished *)
Sorted == \A i \in 1..len-1 : arr[i] <= arr[i+1]

Init ==
  /\ len \in 1..MaxLen
  /\ arr \in [1..len -> 1..MaxVal]
  /\ b   \in [1..len -> 0]
  /\ stack = << [l:1, r:len, phase:"start"] >>

Next ==
  /\ stack # <<>>
  /\ LET top == First(stack) IN
        CASE StartF(top) =>
            IF top.l < top.r THEN
                LET mid == (top.l + top.r) \div 2 IN
                    /\ arr' := arr
                    /\ b'   := b
                    /\ len' := len
                    /\ stack' := Rest(stack) ^ << [l:top.l, r:top.r, mid:mid, phase:"left"] >>
            ELSE
                /\ arr' := arr
                /\ b'   := b
                /\ len' := len
                /\ stack' := Rest(stack)
        [] LeftF(top) =>
            /\ arr' := arr
            /\ b'   := b
            /\ len' := len
            /\ stack' := Rest(stack) ^ << [l:top.l, r:top.r, mid:top.mid, phase:"right"] >>
        [] RightF(top) =>
            /\ arr' := arr
            /\ b'   := b
            /\ len' := len
            /\ stack' := Rest(stack) ^ << [l:top.l, r:top.r, mid:top.mid,
                                           i:top.mid+1, j:top.mid+1, k:top.l, phase:"merge"] >>
        [] MergeF(top) =>
            IF top.k <= top.r THEN
                LET cond == (top.i <= top.mid) /\ (top.j > top.r \/ arr[top.i] <= arr[top.j]) IN
                    /\ b'   := [i \in 1..len |-> IF i = top.k THEN IF cond THEN arr[top.i] ELSE arr[top.j] ELSE b[i]]
                    /\ arr' := arr
                    /\ len' := len
                    /\ stack' := Rest(stack) ^ << [l:top.l, r:top.r, mid:top.mid,
                                                   i: IF cond THEN top.i+1 ELSE top.i,
                                                   j: IF cond THEN top.j ELSE top.j+1,
                                                   k: top.k + 1,
                                                   phase:"merge"] >>
            ELSE
                /\ arr' := [i \in 1..len |-> IF i \in top.l .. top.r THEN b[i] ELSE arr[i]]
                /\ b'   := b
                /\ len' := len
                /\ stack' := Rest(stack)
        ENDCASE

SafetyInv == [] (stack = <<>> => Sorted)

Spec ==
  Init /\ [][Next]_<<arr,b,stack,len>> /\ WF(Next) /\ SafetyInv

=============================================================================