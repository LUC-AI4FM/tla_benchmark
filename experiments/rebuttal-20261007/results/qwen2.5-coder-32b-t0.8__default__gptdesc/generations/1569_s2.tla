------------------------------- MODULE Bakery -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS NumProc
ASSUME NumProc \in Nat /\ NumProc > 0
VARIABLES choosing, number, turn, in_critical_section

(*--algorithm bakery
variables
    choosing = [i \in 1..NumProc |-> FALSE],
    number   = [i \in 1..NumProc |-> 0];

process with process_id \in 1..NumProc
{
    loop:
        choose:
            choosing[process_id] := TRUE;
            number[process_id] := Max(number) + 1;
            choosing[process_id] := FALSE;

        findMax:
            maxima := {number[i] : i \in 1..NumProc};
            local_max := CHOOSE m \in maxima : m = Max(maxima);

        examine:
            with j \in 1..NumProc
                if j /= process_id \/ number[j] # 0 then
                    await not choosing[j];
                    await (number[j] < local_max) \/ 
                          (number[j] = local_max /\ j < process_id);
            
        critical_section:
            in_critical_section := {process_id};
            skip;
            in_critical_section := {};

        noncritical_section:
            number[process_id] := 0;
}
end algorithm
*)

Init == /\ choosing = [i \in 1..NumProc |-> FALSE]
        /\ number   = [i \in 1..NumProc |-> 0]
        /\ in_critical_section = {}

Next ==
    \E process_id \in 1..NumProc :
        \/ \/ choosing[process_id]
           /\ \/ number' = [number EXCEPT ![process_id] = Max(number) + 1]
              /\ choosing' = [choosing EXCEPT ![process_id] = FALSE]
        \/ \A j \in 1..NumProc : 
                (j /= process_id \/ number[j] # 0)
                -> \/ choosing[j] = FALSE
                   /\ (number[j] < Max({number[i] : i \in 1..NumProc}))
                      \/ (number[j] = Max({number[i] : i \in 1..NumProc}) /\ j < process_id)
        \/ in_critical_section = {process_id}
           /\ in_critical_section' = {}
        \/ number[process_id]' = 0

Spec ==
    /\ Init
    /\ [][Next]_<<choosing, number, in_critical_section>>
    /\ <>(\E process_id \in 1..NumProc : in_critical_section = {process_id})

MutualExclusion == 
    \A p, q \in 1..NumProc :
        (p # q) => ~(\E i \in 0..3 : in_critical_section = {p} /\ in_critical_section' = {q})

StateConstraint ==
    \A process_id \in 1..NumProc :
        number[process_id] \leq NumProc

Fairness ==
    WF_<<choosing, number, in_critical_section>>(Next)

THEOREM Spec => []MutualExclusion
THEOREM Spec => StateConstraint

=============================================================================