---- MODULE SANY2ParserTest ----

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    \* Define any necessary constants here

VARIABLES 
    record

Init == 
    /\ record = [ MODULE -> 0, EXTENDS -> 1, CONSTANTS -> 2, VARIABLES -> 3
               , Init -> 4, Next -> 5, Spec -> 6, THEOREM -> 7
               , PROPOSITION -> 8, ASSUME -> 9, INSTANCE -> 10
               , LOCAL -> 11, VARIABLE -> 12, CONSTANT -> 13
               , ASSUMPTION -> 14, AXIOM -> 15, DEFINITION -> 16
               , PROOF -> 17, OBVIOUS -> 18, BY -> 19, PFSTEP -> 20
               , QED -> 21, TAKE -> 22, CHOOSE -> 23, DEFINE -> 24
               , HIDE -> 25, REVEAL -> 26, PROGRESS -> 27 ]

Next == 
    /\ record' = [record EXCEPT !.MODULE = record.MODULE + 1]

Spec == Init /\ [][Next]_<<record>>

THEOREM Spec => []<>(record.MODULE >= 0)

PROPOSITION Spec => [](record.MODULE < 100)

ASSUME Spec => Init

INSTANCE Naturals WITH Nat <- record.MODULE

LOCAL DEF LocalDef == record.MODULE + 1

VARIABLE LocalVar

CONSTANT LocalConst

AXIOM LocalAxiom == LocalConst = 5

DEFINITION LocalDefinition == LocalVar = LocalDef

PROOF
    OBVIOUS
BY DefnIntro, LocalDefinition
PFSTEP Step1: LocalVar = LocalDef
QED

TAKE Step1

CHOOSE x \in {1,2,3} : x > 0

DEFINE 
    LocalMacro(a) == a + 1

HIDE LocalConst

REVEAL LocalConst

PROGRESS Init => Next
========================================