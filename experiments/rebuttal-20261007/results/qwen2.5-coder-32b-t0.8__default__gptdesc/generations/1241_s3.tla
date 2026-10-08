------------------------------- MODULE PlusCalToTLAPlus -------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    -- Constants representing the abstract syntax tree nodes
    Algorithm, Procedure, Process, Statement, Label, Action, Skip, If, While, Call,
    FairnessNone, WeakFairProcessActions, WeakFairNext, StrongFairProcessActions,
    -- Other necessary constants for lexemes and parsing
    Lexeme, Identifier

VARIABLES 
    abstractSyntaxTree,  -- The AST of the PlusCal algorithm
    translatedSpec       -- The resulting TLA+ specification as a sequence of lexemes

Init == 
    /\ abstractSyntaxTree \in [Algorithm: {Algorithm}, Procedures: FiniteSetOf(Procedure), Processes: FiniteSetOf(Process)]
    /\ translatedSpec = <<>>

Next ==
    \/ \E alg \in Algorithm : TranslateAlgorithm(alg)
    \/ \E proc \in Procedures(abstractSyntaxTree) : TranslateProcedure(proc)
    \/ \E proc \in Processes(abstractSyntaxTree) : TranslateProcess(proc)

TranslateAlgorithm(alg) == 
    LET translatedAlg == AppendLexemes("---- MODULE ", alg, " ----")
    IN /\ translatedSpec' = translatedSpec \o translatedAlg

TranslateProcedure(proc) ==
    LET translatedProc == AppendLexemes("PROCEDURE ", proc, "() ==")
    IN /\ translatedSpec' = translatedSpec \o translatedProc

TranslateProcess(proc) ==
    LET translatedProc == AppendLexemes("PROCESS ", proc, " ==")
    IN /\ translatedSpec' = translatedSpec \o translatedProc

AppendLexemes(seq, elem, suffix) ==
    seq \o <<elem>> \o <<suffix>>

FairnessCondition ==
    \/ CASE FairnessNone -> TRUE
    \/ CASE WeakFairProcessActions -> WF_(<<p \in Processes(abstractSyntaxTree): Action(p)>>)
    \/ CASE WeakFairNext -> WF_(<<Next>>)
    \/ CASE StrongFairProcessActions -> SF_(<<p \in Processes(abstractSyntaxTree): Action(p)>>)

Spec ==
    /\ Init
    /\ [][Next]_<<abstractSyntaxTree, translatedSpec>>
    /\ FairnessCondition

Termination ==
    \E sigma \in Seq(translatedSpec) : sigma = AppendLexemes("----", "END_SPECIFICATION", "----")

=============================================================================