---------------------------- MODULE MergeSort ----------------------------
EXTENDS Integers, Naturals

CONSTANT MaxArrayLen
VARIABLE array, temp, len, mid, left, right, done

defaultInitValue == <<0, 0, 0, 0, 0, 0, FALSE>>

Spec == 
  /\ Init
  /\ [][Next]_array
  /\ WF_vars(Next)

Init ==
  /\ array \in [1..MaxArrayLen -> Nat]
  /\ len = Len(array)
  /\ temp = [i \in 1..len |-> 0]
  /\ mid = 0
  /\ left = 0
  /\ right = 0
  /\ done = FALSE

Next ==
  IF done THEN
    UNCHANGED <<array, temp, len, mid, left, right, done>>
  ELSE
    /\ mid = mid + 1
    /\ left = 1
    /\ right = len
    /\ IF mid < len / 2 THEN
        /\ temp' = [i \in 1..len |-> 
            IF i = left THEN array[left]
            ELSE IF i = right THEN array[right]
            ELSE temp[i]]
        /\ array' = [i \in 1..len |-> 
            IF i = left THEN temp[left]
            ELSE IF i = right THEN temp[right]
            ELSE array[i]]
        /\ len' = len
        /\ done' = FALSE
      ELSE
        /\ temp' = temp
        /\ array' = Merge(array, temp, 1, len)
        /\ len' = len
        /\ done' = TRUE
    /\ UNCHANGED <<temp, left, right>>

Merge(arr, tmp, l, r) ==
  IF l >= r THEN arr
  ELSE
    /\ mid == (l + r) / 2
    /\ leftArr == [i \in l..mid |-> arr[i]]
    /\ rightArr == [i \in mid+1..r |-> arr[i]]
    /\ merged == MergeRec(leftArr, rightArr)
    /\ [i \in l..r |-> IF i <= mid THEN merged[i-l+1] ELSE merged[i-mid]]

MergeRec(left, right) ==
  IF left = <<>> OR right = <<>> THEN
    left ++ right
  ELSE
    /\ lh == Head(left)
    /\ rh == Head(right)
    /\ IF lh <= rh THEN
        <<lh>> ++ MergeRec(Tail(left), right)
      ELSE
        <<rh>> ++ MergeRec(left, Tail(right))

Invariant ==
  /\ array \in [1..MaxArrayLen -> Nat]
  /\ temp \in [1..MaxArrayLen -> Nat]
  /\ len \in 0..MaxArrayLen
  /\ mid \in 0..MaxArrayLen
  /\ left \in 0..MaxArrayLen
  /\ right \in 0..MaxArrayLen
  /\ done \in {TRUE, FALSE}

Termination == done

THEOREM Spec => []Invariant
THEOREM Spec => <><Termination
=============================================================================