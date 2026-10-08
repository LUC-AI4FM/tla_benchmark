---- MODULE SimplePlusCalExample ----

EXTENDS Integers, Sequences, FiniteSets

VARIABLES setVar, seqVar

CONSTANTS NewStringElement, NewSequenceValue

(*--algorithm SimplePlusCalExample
variables setVar = {"initial1", "initial2"},
          seqVar = <<1, 2, 3>>;

begin
    with \* Adding a new string element to the set
        print "Initial setVar: ", setVar;
        setVar := setVar \cup {NewStringElement};
        print "Updated setVar: ", setVar;

        \* Replacing the second element of the sequence
        print "Initial seqVar: ", seqVar;
        seqVar := [seqVar EXCEPT ![2] = NewSequenceValue];
        print "Updated seqVar: ", seqVar;
    end with;
    
    print "Done";
end algorithm;*)

Spec == /\ Init
        /\ \A s \in StateTrace : s' \in Next(s)

Init == /\ setVar = {"initial1", "initial2"}
        /\ seqVar = <<1, 2, 3>>

Next ==
    \/ /\ UNCHANGED setVar
       /\ seqVar' = [seqVar EXCEPT ![2] = NewSequenceValue]
    \/ /\ setVar' = setVar \cup {NewStringElement}
       /\ UNCHANGED seqVar

StateTrace == <<s0>> \o <<s \in States : s' \in Next(s)>>

States == INSTANCE Fairness!FairStates(<<Init>>, Next)

====