------------------------------- MODULE PlusCalExample -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS 
    InitialSet, InitialSeq

VARIABLES 
    setVar, seqVar, done

Init == 
    /\ setVar = InitialSet
    /\ seqVar = InitialSeq
    /\ done = FALSE

Next ==
    \/ /\ ~done
       /\ setVar' = setVar \cup {"newElement"}
       /\ seqVar' = [seqVar EXCEPT ![1] = 42]
       /\ done'
       /\ PrintT(setVar')
       /\ Print(seqVar')
    \/ /\ done
       /\ UNCHANGED <<setVar, seqVar, done>>

Spec == 
    Init /\ [][Next]_<<setVar, seqVar, done>> /\ <><Done>_\<<setVar, seqVar, done>>

Done == done

=============================================================================