------------------------------- MODULE TwoComponentSystem -------------------------------

CONSTANTS 
    \* The specific nonzero value to set as result and remove from sequence
    NEW_RESULT

VARIABLES 
    \* Shared sequence of integers
    sequence,
    \* Shared result variable
    result

(*--algorithm TwoComponentSystem
variables sequence = <<1, 2, 3>>, result = 0;

fair process InnerService \in 1..1
begin
    while TRUE do
        if result = 0 then
            result := NEW_RESULT;
            sequence := [s \in sequence | s # NEW_RESULT];
        end if;
        await FALSE; \* Stay in this state forever after the action is done
    end while;
end process;

process OuterController \in 1..1
begin
    while TRUE do
        await result = NEW_RESULT; \* Stutter when InnerService is not enabled
    end while;
end process;
end algorithm*)

Spec == 
    /\ TYPEOK(sequence, <<>>) 
    /\ sequence \in SUBSET (Nat \ {0}) 
    /\ Len(sequence) > 0 
    /\ result \in {0} \cup {NEW_RESULT}
    /\ Init /\ [][Next]_<<InnerService, OuterController>>
    
Init == 
    /\ sequence = <<1, 2, 3>> 
    /\ result = 0

Next ==
    \/ /\ PC[InnerService] = "InnerService"
       /\ result = 0
       /\ result' = NEW_RESULT
       /\ sequence' = [s \in sequence | s # NEW_RESULT]
       /\ UNCHANGED <<PC[OuterController]>>
    \/ /\ PC[InnerService] = "await FALSE"
       /\ result = NEW_RESULT
       /\ UNCHANGED <<result, sequence>>
       /\ PC'[InnerService] = "await FALSE"
       /\ UNCHANGED <<PC[OuterController]>>

SpecRunsToEnd ==
    <>(result = NEW_RESULT) /\ [](result = NEW_RESULT => UNCHANGED <<sequence, result>>)

THEOREM Spec => []<>(result = NEW_RESULT)
THEOREM Spec => [](result = NEW_RESULT => UNCHANGED <<sequence, result>>)

=============================================================================