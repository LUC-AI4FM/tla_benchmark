```
MODULE Translation
EXTENDS Integers, Sequences, TLC

CONSTANTS Stmt, Expr, Label, Proc
VARIABLES ast, translation, fairness

Init == 
  /\ ast = << >>
  /\ translation = << >>
  /\ fairness = "no_fairness"

Next == 
  /\ IF fairness = "no_fairness" THEN 
    /\ ast' = ast
    /\ translation' = TranslationPipeline(ast)
    /\ fairness' = fairness
  ELSE IF fairness = "weak_process" THEN 
    /\ ast' = ast
    /\ translation' = TranslationPipeline(ast)
    /\ fairness' = fairness
    /\ WeakFairnessProcess(translation')
  ELSE IF fairness = "weak_next" THEN 
    /\ ast' = ast
    /\ translation' = TranslationPipeline(ast)
    /\ fairness' = fairness
    /\ WeakFairnessNext(translation')
  ELSE IF fairness = "strong_process" THEN 
    /\ ast' = ast
    /\ translation' = TranslationPipeline(ast)
    /\ fairness' = fairness
    /\ StrongFairnessProcess(translation')
  END

TranslationPipeline(s) == 
  LET exploded == ExplodeStructuredStmts(s)
  IN AddSubscriptsForLocals(exploded)

ExplodeStructuredStmts(s) == 
  IF s.type = "While" THEN 
    << s.label, s.cond >> @@ ExplodeStructuredStmts(s.body)
  ELSE IF s.type = "If" THEN 
    << s.label, s.cond >> @@ ExplodeStructuredStmts(s.thenBranch)
      @@ ExplodeStructuredStmts(s.elseBranch)
  ELSE s

AddSubscriptsForLocals(s) == 
  [x \in DOMAIN s |-> IF x.type = "Var" THEN x.name || "_sub" ELSE x]

WeakFairnessProcess(t) == 
  \A p \in Procs : <>[]<p>.t[p] /= t'[p]

WeakFairnessNext(t) == 
  <>[]t /= t'

StrongFairnessProcess(t) == 
  \A p \in Procs : []<> <p>.t[p] /= t'[p]

Spec == Init /\ [][Next]_ast

Termination == <>(translation = <<>>)

THEOREM Spec => []Termination
```