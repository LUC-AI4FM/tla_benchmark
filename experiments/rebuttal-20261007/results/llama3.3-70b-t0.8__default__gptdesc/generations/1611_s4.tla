```
MODULE Mergesort
EXTENDS Integers, Sequences

CONSTANTS ArrayLen, N
VARIABLES pc, array, b, callStack, idx

Init == 
  /\ pc = "Start"
  /\ array \in [1..N]^ArrayLen
  /\ b = <<>>
  /\ callStack = <<>>
  /\ idx = 0

Next == 
  IF pc = "Start" THEN
    /\ pc' = "Sort"
    /\ callStack' = <<[idx |-> 0, len |-> ArrayLen]>>
    /\ array' = array
    /\ b' = b
    /\ idx' = idx
  ELSE IF pc = "Sort" THEN
    /\ IF HD callStack.len = 1 THEN 
        /\ pc' = "Done"
        /\ array' = array
        /\ b' = b
        /\ callStack' = TL callStack
        /\ idx' = idx + 1
      ELSE 
        /\ WITH arg == HD callStack
          DO 
            /\ IF arg.len <= 1 THEN 
                /\ pc' = "Sort"
                /\ callStack' = <<[idx |-> arg.idx, len |-> arg.len]>> @@ TL callStack
                /\ array' = array
                /\ b' = b
                /\ idx' = idx + 1
              ELSE 
                /\ mid == arg.len DIV 2
                /\ pc' = "Split"
                /\ callStack' = <<[idx |-> arg.idx, len |-> mid]>> @@ <<[idx |-> arg.idx + mid, len |-> arg.len - mid]>> @@ TL callStack
                /\ array' = array
                /\ b' = b
                /\ idx' = idx
    /\ idx' = idx
  ELSE IF pc = "Split" THEN 
    /\ WITH arg == HD callStack
      DO 
        /\ mid == arg.len DIV 2
        /\ leftHalf == <<>>
        /\ rightHalf == <<>>
        /\ idxTemp == arg.idx
        /\ FOR i \in 1..mid
          DO 
            /\ leftHalf' = Append(leftHalf, array[idxTemp])
            /\ idxTemp' = idxTemp + 1
        /\ FOR i \in mid+1..arg.len
          DO 
            /\ rightHalf' = Append(rightHalf, array[idxTemp])
            /\ idxTemp' = idxTemp + 1
        /\ b' = leftHalf @@ rightHalf
        /\ pc' = "Merge"
        /\ callStack' = TL callStack
        /\ array' = array
        /\ idx' = idx
  ELSE IF pc = "Merge" THEN 
    /\ WITH arg == HD callStack, left == b[1], right == b[len(b) - len(left)]
      DO 
        /\ merged == Merge(left, right)
        /\ pc' = "Sort"
        /\ array' = Replace(array, idx..(idx + len(left) + len(right) - 1), merged)
        /\ b' = <<>>
        /\ callStack' = TL callStack
        /\ idx' = idx

Spec == 
  /\ Init
  /\ [][Next]_array
  /\ WF_vars(Next)

MergeSortInvar == 
  /\ pc \in {"Start", "Sort", "Split", "Merge", "Done"}
  /\ callStack \in Seq([idx: Int, len: Int])
  /\ array \in [1..N]^ArrayLen
  /\ b \in Seq([1..N])

Sorted == 
  /\ \A i, j \in 1..ArrayLen : i < j => array[i] <= array[j]

THEOREM Spec => []Sorted
```