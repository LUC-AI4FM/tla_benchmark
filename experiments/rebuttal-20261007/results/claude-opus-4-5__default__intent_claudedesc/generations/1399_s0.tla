---------------------------- MODULE Toggle ----------------------------
EXTENDS Booleans

VARIABLES flag

Init == flag = TRUE

Next == flag' = ~flag

Spec == Init /\ [][Next]_flag

TypeInvariant == flag \in BOOLEAN

AlwaysTrue == flag = TRUE

TriviallyTrue == TRUE

FlagProperty == flag

Invariant == flag = TRUE

EventuallyTrue == <>flag

EventuallyFalse == <>(~flag)

AlwaysEventuallyTrue == []<>flag

AlwaysEventuallyFalse == []<>(~flag)

FairSpec == Init /\ [][Next]_flag /\ WF_flag(Next)

=======================================================================