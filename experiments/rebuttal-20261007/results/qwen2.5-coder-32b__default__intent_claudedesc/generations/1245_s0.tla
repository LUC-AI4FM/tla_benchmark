------------------------------- MODULE CalToTlaTranslator -------------------------------
EXTENDS Sequences, FiniteSets, TLC

CONSTANTS 
    -- Constants for the grammar rules
    PROCEDURE, PROCESS, VAR, LABEL, WHILE, IF, EITHER, WITH, CALL, RETURN, COMBINED_CALL_RETURN, GOTO, ASSIGNMENT, WHEN, PRINT, ASSERT, SKIP,
    -- Fairness options
    NONE, WEAK_FAIRNESS_PER_ACTION, WEAK_FAIRNESS_WHOLE_NEXT_STATE, STRONG_FAIRNESS_PER_ACTION

VARIABLES 
    ast, fairnessOption, lexemes, pc, stack, variables, labels, actions, nextAction, spec, termination

Init == 
    /\ ast \in [algorithmType: {"uniprocess", "multiprocess"}, declarations: seqOfDeclarations, body: seqOfStatements]
    /\ fairnessOption \in {NONE, WEAK_FAIRNESS_PER_ACTION, WEAK_FAIRNESS_WHOLE_NEXT_STATE, STRONG_FAIRNESS_PER_ACTION}
    /\ lexemes = <<>>
    /\ pc = 0
    /\ stack = <<>>
    /\ variables = {}
    /\ labels = {}
    /\ actions = [label \in DOMAIN ast.body |-> {}]
    /\ nextAction = {}
    /\ spec = TRUE
    /\ termination = FALSE

Next == 
    \/ /\ pc < Len(ast.body)
       /\ LET statement = ast.body[pc + 1] IN
          CASE IsProcedure(statement) -> [][pc' = pc + 1]_<<lexemes', stack'> \in PushProcedure(statement, lexemes, stack)>>
             [] IsProcess(statement) -> [][pc' = pc + 1]_<<lexemes', stack'> \in PushProcess(statement, lexemes, stack)>>
             [] IsVarDeclaration(statement) -> [][pc' = pc + 1]_<<lexemes', variables'> \in AddVariables(statement, lexemes, variables)>>
             [] IsLabel(statement) -> [][pc' = pc + 1]_<<lexemes', labels'> \in AddLabel(statement, lexemes, labels)>>
             [] IsWhileLoop(statement) -> [][pc' = pc + 1]_<<lexemes', actions'> \in AddWhileLoop(statement, lexemes, actions)>>
             [] IsIfEitherWith(statement) -> [][pc' = pc + 1]_<<lexemes', actions'> \in AddIfEitherWith(statement, lexemes, actions)>>
             [] IsCall(statement) -> [][pc' = pc + 1]_<<lexemes', stack'> \in PushCall(statement, lexemes, stack)>>
             [] IsReturn(statement) -> [][pc' = pc + 1]_<<lexemes', stack'> \in PopStack(statement, lexemes, stack)>>
             [] IsCombinedCallReturn(statement) -> [][pc' = pc + 1]_<<lexemes', stack'> \in HandleCombinedCallReturn(statement, lexemes, stack)>>
             [] IsGoto(statement) -> [][pc' = pc + 1]_<<lexemes', actions'> \in AddGoto(statement, lexemes, actions)>>
             [] IsSimpleStatement(statement) -> [][pc' = pc + 1]_<<lexemes', actions'> \in AddSimpleStatement(statement, lexemes, actions)>>
    \/ /\ pc = Len(ast.body)
       /\ spec = SpecFormula()
       /\ termination = TerminationProperty()

Spec == Init /\ [][Next]_<<lexemes, pc, stack, variables, labels, actions, nextAction, spec, termination>>

Fairness ==
    CASE fairnessOption = NONE -> TRUE
       [] fairnessOption = WEAK_FAIRNESS_PER_ACTION -> WF_vars(<<pc>>, Next)
       [] fairnessOption = WEAK_FAIRNESS_WHOLE_NEXT_STATE -> WF_vars(<<lexemes, pc, stack, variables, labels, actions, nextAction, spec, termination>>, Next)
       [] fairnessOption = STRONG_FAIRNESS_PER_ACTION -> SF_vars(<<pc>>, Next)

CompleteSpec == Spec /\ Fairness

=============================================================================