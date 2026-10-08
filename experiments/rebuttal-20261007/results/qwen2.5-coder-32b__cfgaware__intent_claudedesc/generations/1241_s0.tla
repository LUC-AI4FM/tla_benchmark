---- MODULE PlusCalTranslation ----

CONSTANTS Object, Any

(*--algorithm PlusCalGrammar
variables pc, stack;

begin
  Init == /\ pc = "start"
         /\ stack = << >>

  Next ==
    \/ \E stmt \in statements: Execute(stmt)

  Execute(stmt) ==
    CASE stmt.type = "assign" -> Assign(stmt)
       [] stmt.type = "call"   -> Call(stmt)
       [] stmt.type = "return" -> Return()
       [] stmt.type = "if"     -> If(stmt)
       [] stmt.type = "while"   -> While(stmt)
       [] stmt.type = "goto"    -> Goto(stmt)
       [] stmt.type = "when"    -> When(stmt)
       [] stmt.type = "print"   -> Print(stmt)
       [] stmt.type = "assert"  -> Assert(stmt)
       [] stmt.type = "skip"    -> Skip()

  Assign(stmt) ==
    /\ pc' = stmt.label
    /\ vars[stmt.variable] = stmt.expression

  Call(stmt) ==
    /\ stack' = Append(stack, <<pc, stmt.procedure>>)
    /\ pc' = stmt.label

  Return() ==
    /\ LET top == Head(stack)
       IN /\ pc' = top[1]
          /\ stack' = Tail(stack)

  If(stmt) ==
    \/ stmt.condition -> Execute(stmt.thenStmt)
    [] ~stmt.condition -> Execute(stmt.elseStmt)

  While(stmt) ==
    \/ stmt.condition -> Execute(stmt.body)
    [] ~stmt.condition -> pc' = stmt.label

  Goto(stmt) ==
    pc' = stmt.targetLabel

  When(stmt) ==
    /\ stmt.expression
    /\ pc' = stmt.label

  Print(stmt) ==
    /\ print stmt.message
    /\ pc' = stmt.label

  Assert(stmt) ==
    \/ stmt.condition -> pc' = stmt.label
    [] ~stmt.condition -> ERROR

  Skip() ==
    pc' = stmt.label

end algorithm *)

Translation(alg, fairnessOption) == << "---- MODULE ", alg.name, " ----",
                                      "\n\nCONSTANTS Object, Any\n\nVARIABLES ",
                                      StringSetToString({v \in DOMAIN alg.variables}),
                                      ", pc, stack\n\nInit == ",
                                      InitDefinition(alg),
                                      "\n\nNext == ",
                                      NextDefinition(alg.statements),
                                      FairnessDefinition(fairnessOption),
                                      "\n\nTermination == <>[]<>\\A p \\in ProcSet: ~Running(p)\n\n---- END MODULE ----" >>

InitDefinition(alg) ==
  " /\ pc = \"start\""
  \o (IF alg.type = "multiprocess"
      THEN " /\ stack = << >>\n    /\ ProcSet = {" & StringSetToString({p \in DOMAIN alg.processes}) & "}\n    /\ \\A p \\in ProcSet: vars[p] = [" & StringSetToString({v \in DOMAIN alg.variables}) & " |-> ?]"
      ELSE " /\ stack = << >>")

NextDefinition(statements) ==
  " \/ " & SeqToString(SeqMap(StatementTranslation, statements))

FairnessDefinition(fairnessOption) ==
  CASE fairnessOption = "no fairness" -> ""
       [] fairnessOption = "weak process actions" -> "\n\nWF_PROC == WF_(<<", StringSetToString({p \in ProcSet: Running(p)}), ">>, Next)\n\nSpec == Init /\ [][Next]_<<", StringSetToString({p \in ProcSet}), ">>\n\nTHEOREM Spec => WF_PROC"
       [] fairnessOption = "weak next action" -> "\n\nWF_NEXT == WF_(Next, <<", StringSetToString({p \in ProcSet: Running(p)}), ">>)\n\nSpec == Init /\ [][Next]_<<", StringSetToString({p \in ProcSet}), ">>\n\nTHEOREM Spec => WF_NEXT"
       [] fairnessOption = "strong process actions" -> "\n\nSF_PROC == SF_(<<", StringSetToString({p \in ProcSet: Running(p)}), ">>, Next)\n\nSpec == Init /\ [][Next]_<<", StringSetToString({p \in ProcSet}), ">>\n\nTHEOREM Spec => SF_PROC"

StatementTranslation(stmt) ==
  CASE stmt.type = "assign" -> AssignTranslation(stmt)
       [] stmt.type = "call"   -> CallTranslation(stmt)
       [] stmt.type = "return" -> ReturnTranslation()
       [] stmt.type = "if"     -> IfTranslation(stmt)
       [] stmt.type = "while"   -> WhileTranslation(stmt)
       [] stmt.type = "goto"    -> GotoTranslation(stmt)
       [] stmt.type = "when"    -> WhenTranslation(stmt)
       [] stmt.type = "print"   -> PrintTranslation(stmt)
       [] stmt.type = "assert"  -> AssertTranslation(stmt)
       [] stmt.type = "skip"    -> SkipTranslation(stmt)

AssignTranslation(stmt) ==
  "pc' = \"" & stmt.label & "\" /\ vars[" & stmt.variable & "] = " & stmt.expression

CallTranslation(stmt) ==
  "stack' = Append(stack, <<pc, \"" & stmt.procedure & "\">>) /\ pc' = \"" & stmt.label & "\""

ReturnTranslation() ==
  "LET top == Head(stack) IN pc' = top[1] /\ stack' = Tail(stack)"

IfTranslation(stmt) ==
  "(IF " & stmt.condition & " THEN " & StatementTranslation(stmt.thenStmt)
  \o (IF stmt.elseStmt # [] THEN " ELSE " & StatementTranslation(stmt.elseStmt) ELSE "") & " ENDIF)"

WhileTranslation(stmt) ==
  "(IF " & stmt.condition & " THEN " & StatementTranslation(stmt.body) & " ELSE pc' = \"" & stmt.label & "\")"

GotoTranslation(stmt) ==
  "pc' = \"" & stmt.targetLabel & "\""

WhenTranslation(stmt) ==
  "(" & stmt.expression & " => pc' = \"" & stmt.label & "\")"

PrintTranslation(stmt) ==
  "print(" & stmt.message & ") /\ pc' = \"" & stmt.label & "\""

AssertTranslation(stmt) ==
  "(IF " & stmt.condition & " THEN pc' = \"" & stmt.label & "\" ELSE ERROR)"

SkipTranslation(stmt) ==
  "pc' = \"" & stmt.label & "\""

StringSetToString(set) == SeqToString(SeqSort(SET_TO_SEQ(set)))

SeqToString(seq) == CHOOSE s \in STRING: s = "" \/ /\ Len(s) = Len(seq)
                                                   /\ \A i \in 1..Len(seq): s[i] = IF i # 1 THEN ", " & seq[i] ELSE seq[i]

Running(p) ==
  p \in ProcSet /\ pc[p] # "done"

====