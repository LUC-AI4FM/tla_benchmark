------------------------------- MODULE TwoWorkersIncrement -------------------------------

CONSTANTS Worker1, Worker2

VARIABLES counter, finished

(*--algorithm TwoWorkersIncrement
variables 
    counter = 0,
    finished = {};

process (Worker \in {Worker1, Worker2})
begin
    if Worker \notin finished then
        counter := counter + 1;
        finished := finished \cup {Worker}
    end if;
end process;

end algorithm;*)

Spec == /\ TYPEOK
        /\ Init /\ [][Next]_<<counter, finished>>
        /\ WF_next(<<counter, finished>>)

Init == /\ counter = 0
        /\ finished = {}

Next == \/ \E Worker \in {Worker1, Worker2} : 
                /\ Worker \notin finished
                /\ counter' = counter + 1
                /\ finished' = finished \cup {Worker}
           \/ /\ UNCHANGED counter
              /\ UNCHANGED finished

WF_next(vars) == WF_vars(Next)

TYPEOK == /\ counter \in Int
          /\ finished \subseteq {Worker1, Worker2}

Termination == finished = {Worker1, Worker2}

FinalCounterValue == counter = 2

THEOREM Spec => []TypeOK /\ <>Termination /\ <>([]FinalCounterValue)

=============================================================================