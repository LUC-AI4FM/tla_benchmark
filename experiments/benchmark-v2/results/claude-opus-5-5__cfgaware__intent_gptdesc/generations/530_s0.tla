------------------------------- MODULE FindMax -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Tuples, minValue

ASSUME minValue \in Int
ASSUME \A t \in Tuples : \A n \in 1..Len(t) : t[n] \in Int /\ t[n] >= minValue

VARIABLES inp, max, i, pc

vars == << inp, max, i, pc >>

RangeOf(s) == { s[k] : k \in 1..Len(s) }

Init ==
    /\ inp \in Tuples
    /\ max = minValue
    /\ i = 1
    /\ pc = "Pre"

\* Precondition check: every element strictly greater than minValue
Pre ==
    /\ pc = "Pre"
    /\ Assert(\A n \in 1..Len(inp) : inp[n] > minValue,
              "Failure of precondition: element not greater than minValue")
    /\ pc' = "Loop"
    /\ UNCHANGED << inp, max, i >>

\* Loop guard
Loop ==
    /\ pc = "Loop"
    /\ IF i <= Len(inp)
          THEN pc' = "Body"
          ELSE pc' = "Post"
    /\ UNCHANGED << inp, max, i >>

\* Loop body: update running maximum and advance index
Body ==
    /\ pc = "Body"
    /\ IF max < inp[i]
          THEN max' = inp[i]
          ELSE max' = max
    /\ i' = i + 1
    /\ pc' = "Loop"
    /\ UNCHANGED inp

\* Postcondition assertion upon termination
Post ==
    /\ pc = "Post"
    /\ Assert(IF Len(inp) = 0
                 THEN max = minValue
                 ELSE /\ max \in RangeOf(inp)
                      /\ \A n \in 1..Len(inp) : inp[n] <= max,
              "Failure of postcondition")
    /\ pc' = "Done"
    /\ UNCHANGED << inp, max, i >>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Pre \/ Loop \/ Body \/ Post \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Liveness
Termination == <>(pc = "Done")

\* Safety properties
TypeOK ==
    /\ inp \in Tuples
    /\ max \in Int
    /\ i \in 1..(Len(inp) + 1)
    /\ pc \in {"Pre", "Loop", "Body", "Post", "Done"}

MaxAtLeastMin == max >= minValue

LoopDone == pc \in {"Post", "Done"}

MaxIsElement ==
    LoopDone =>
        IF Len(inp) = 0
           THEN max = minValue
           ELSE max \in RangeOf(inp)

MaxIsUpperBound ==
    LoopDone => \A n \in 1..Len(inp) : inp[n] <= max

\* Running invariant: max is the largest of the elements seen so far
RunningMax ==
    pc \in {"Loop", "Body"} =>
        /\ \A n \in 1..(i - 1) : inp[n] <= max
        /\ (i = 1 => max = minValue)
        /\ (i > 1 => max \in { inp[n] : n \in 1..(i - 1) })

Correctness == MaxAtLeastMin /\ MaxIsElement /\ MaxIsUpperBound
=============================================================================