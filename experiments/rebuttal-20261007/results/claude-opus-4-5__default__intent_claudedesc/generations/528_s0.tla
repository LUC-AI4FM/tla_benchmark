---------------------------- MODULE PlusCalDemo ----------------------------
EXTENDS Sequences, Integers, TLC

(* --algorithm demo
variables
    mySet = {"apple", "banana"},
    mySeq = <<1, 2, 3>>;

begin
    AddToSet:
        mySet := mySet \union {"cherry"};
        print mySet;
    
    UpdateSeq:
        mySeq := [mySeq EXCEPT ![2] = 99];
        print mySeq;
    
    Done:
        skip;

end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "e8d13a4e" /\ chksum(tla) = "4a6e75c8")
VARIABLES mySet, mySeq, pc

vars == << mySet, mySeq, pc >>

Init == (* Global variables *)
        /\ mySet = {"apple", "banana"}
        /\ mySeq = <<1, 2, 3>>
        /\ pc = "AddToSet"

AddToSet == /\ pc = "AddToSet"
            /\ mySet' = (mySet \union {"cherry"})
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

Next == AddToSet \/ UpdateSeq \/ Done

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION

\* Safety invariant: mySet always contains at least the original elements
SetContainsOriginals == {"apple", "banana"} \subseteq mySet

\* Safety invariant: mySeq always has length 3
SeqLengthInvariant == Len(mySeq) = 3

\* Liveness property: execution eventually terminates (reaches Done state)
EventuallyTerminates == <>(pc = "Done")

\* Combined type invariant
TypeInvariant == 
    /\ mySet \subseteq {"apple", "banana", "cherry"}
    /\ Len(mySeq) = 3

=============================================================================