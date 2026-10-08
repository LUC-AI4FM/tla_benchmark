---------------------------- MODULE specification ----------------------------

EXTENDS Integers, Sequences, TLC

(* --algorithm BasicPlusCal
variables
    mySet = {"a", "b"},
    mySeq = <<1, 2, 3>>;

begin
    UpdateSet:
        mySet := mySet \union {"c"};
        print mySet;
    
    UpdateSeq:
        mySeq := [mySeq EXCEPT ![2] = 99];
        print mySeq;
    
    Done:
        skip;

end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "99444b62" /\ chksum(tla) = "59002fbc")
VARIABLES mySet, mySeq, pc

vars == << mySet, mySeq, pc >>

Init == (* Global variables *)
        /\ mySet = {"a", "b"}
        /\ mySeq = <<1, 2, 3>>
        /\ pc = "UpdateSet"

UpdateSet == /\ pc = "UpdateSet"
             /\ mySet' = (mySet \union {"c"})
             /\ PrintT(mySet')
             /\ pc' = "UpdateSeq"
             /\ mySeq' = mySeq

UpdateSeq == /\ pc = "UpdateSeq"
             /\ mySeq' = [mySeq EXCEPT ![2] = 99]
             /\ PrintT(mySeq')
             /\ pc' = "Done"
             /\ mySet' = mySet

Done == /\ pc = "Done"
        /\ TRUE
        /\ pc' = "Done"
        /\ UNCHANGED << mySet, mySeq >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == UpdateSet \/ UpdateSeq \/ Done \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

=============================================================================