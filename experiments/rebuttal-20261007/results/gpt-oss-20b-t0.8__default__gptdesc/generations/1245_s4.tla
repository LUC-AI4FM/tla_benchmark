MODULE Translation

EXTENDS Sequences, TLC

CONSTANTS FAIRNESS   \* Options: "none", "weakProc", "weakNext", "strongProc"

VARIABLES stage, AST, ExposedAST, CallsTranslated, SubscriptsAdded, FinalSpec

(* Types and placeholder predicates *)
Stmt == [type : STRING]
Stmts == Seq(Stmt)
ASTNode == [stmts : Stmts]

(* Placeholder translation functions *)
Explode(ast)      == ast.stmts
TranslateCalls(seq) == seq
AddSubs(seq)      == seq

Init ==
  /\ stage = "explode"
  /\ AST = [stmts |-> <<>>]
  /\ ExposedAST = <<>>
  /\ CallsTranslated = <<>>
  /\ SubscriptsAdded = <<>>
  /\ FinalSpec = <<>>

Next ==
  \/ /\ stage = "explode"
     /\ ExposedAST' = Explode(AST)
     /\ stage' = "translateCalls"
     /\ AST' = AST
     /\ CallsTranslated' = CallsTranslated
     /\ SubscriptsAdded' = SubscriptsAdded
     /\ FinalSpec' = FinalSpec
  \/ /\ stage = "translateCalls"
     /\ CallsTranslated' = TranslateCalls(ExposedAST)
     /\ stage' = "addSubs"
     /\ ExposedAST' = ExposedAST
     /\ AST' = AST
     /\ SubscriptsAdded' = SubscriptsAdded
     /\ FinalSpec' = FinalSpec
  \/ /\ stage = "addSubs"
     /\ SubscriptsAdded' = AddSubs(CallsTranslated)
     /\ stage' = "done"
     /\ CallsTranslated' = CallsTranslated
     /\ ExposedAST' = ExposedAST
     /\ AST' = AST
     /\ FinalSpec' = FinalSpec
  \/ /\ stage = "done"
     /\ FinalSpec' = SubscriptsAdded
     /\ stage' = "done"        \* stay in done
     /\ AST' = AST
     /\ ExposedAST' = ExposedAST
     /\ CallsTranslated' = CallsTranslated
     /\ SubscriptsAdded' = SubscriptsAdded

Vars == <<stage, AST, ExposedAST, CallsTranslated, SubscriptsAdded, FinalSpec>>

Safe == stage ∈ {"explode","translateCalls","addSubs","done"}

Termination == <> (stage = "done")

Spec == Init
        /\ [][Next]_Vars
        /\ Safe

FairnessCond ==
  CASE FAIRNESS = "none" -> TRUE
       \/ FAIRNESS = "weakProc" -> WeakFairness(Next)
       \/ FAIRNESS = "weakNext" -> WeakFairness(Next)
       \/ FAIRNESS = "strongProc" -> StrongFairness(Next)

============================================================================