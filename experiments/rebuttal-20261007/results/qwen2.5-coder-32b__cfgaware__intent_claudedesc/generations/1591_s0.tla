------------------------------- MODULE EvenOdd -------------------------------

CONSTANTS N

VARIABLES pc, countEvenToOdd, countOdd

(*--algorithm EvenOdd {
    variables pc = "start", countEvenToOdd = 0, countOdd = 0;

    start:
        if N = 6 then /\ pc' = "even"
                     /\ countEvenToOdd' = 0
                     /\ countOdd' = 0
        else skip;

    even:
        if pc = "even" then
            if N = 0 then /\ pc' = "done"
                          /\ print(TRUE)
            else /\ pc' = "odd"
                 /\ N' = N - 1
                 /\ countEvenToOdd' = countEvenToOdd + 1;

    odd:
        if pc = "odd" then
            if N = 0 then /\ pc' = "done"
                          /\ print(FALSE)
            else /\ pc' = "even"
                 /\ N' = N - 1
                 /\ countOdd' = countOdd + 1;

    done:
        if pc = "done" then /\ pc' = "done";
}*)

Spec == 
    /\ Init
    /\ [][Next]_<<pc, N, countEvenToOdd, countOdd>>
    /\ \A s \in States: Inv(s)

Init ==
    /\ pc = "start"
    /\ countEvenToOdd = 0
    /\ countOdd = 0

Next ==
    \/ pc = "start" -> [][Start]_<<pc, N, countEvenToOdd, countOdd>>
    \/ pc = "even"  -> [][Even]_<<pc, N, countEvenToOdd, countOdd>>
    \/ pc = "odd"   -> [][Odd]_<<pc, N, countEvenToOdd, countOdd>>
    \/ pc = "done"

Start ==
    /\ N = 6
    /\ pc' = "even"
    /\ countEvenToOdd' = 0
    /\ countOdd' = 0

Even ==
    /\ pc = "even"
    /\ (N = 0 -> [][Done(TRUE)]_<<pc, N, countEvenToOdd, countOdd>>)
    /\ (N > 0 -> [][Transition("odd", N - 1, countEvenToOdd + 1)]_<<pc, N, countEvenToOdd, countOdd>>)

Odd ==
    /\ pc = "odd"
    /\ (N = 0 -> [][Done(FALSE)]_<<pc, N, countEvenToOdd, countOdd>>)
    /\ (N > 0 -> [][Transition("even", N - 1, countOdd + 1)]_<<pc, N, countEvenToOdd, countOdd>>)

Done(result) ==
    /\ pc' = "done"
    /\ UNCHANGED <<N, countEvenToOdd, countOdd>>
    /\ print(result)

Transition(newPc, newN, newCount) ==
    /\ pc' = newPc
    /\ N' = newN
    /\ IF newPc = "odd" THEN countOdd' = newCount ELSE countEvenToOdd' = newCount

Inv(s) == 
    \/ s.pc = "start"
    \/ s.pc = "even"
    \/ s.pc = "odd"
    \/ s.pc = "done"

Termination ==
    \A s \in States: s.pc = "done" => <s.countEvenToOdd, s.countOdd> = <<3, 3>>

States == 
    { s \in [pc : {"start", "even", "odd", "done"}, N : NATURAL, countEvenToOdd : NATURAL, countOdd : NATURAL] :
        \/ s.pc = "start"
        \/ (s.pc = "even" /\ s.N >= 0)
        \/ (s.pc = "odd" /\ s.N > 0)
        \/ s.pc = "done" }

print(result) == UNCHANGED <<pc, N, countEvenToOdd, countOdd>>

=============================================================================