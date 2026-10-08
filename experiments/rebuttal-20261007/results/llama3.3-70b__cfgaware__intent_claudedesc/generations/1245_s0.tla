---------------------------- MODULE CALTranslator ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Object, Any

VARIABLE calAST, fairnessOption, tlaSpec

calAST == [ type |-> "Algorithm", 
            body |-> << >>
          ]

fairnessOption == "none" \/ "weakPerAction" \/ "weakWholeNext" \/ "strongPerAction"

TypeOK(cal) == cal.type = "Algorithm"
              /\ cal.body \in Seq(Stmt)

Stmt == { "Proc", "Process", "VarDecl", "Label", "While", "If", "Either", "With", 
          "Call", "Return", "Goto", "Assign", "When", "Print", "Assert", "Skip" }

Translation(cal, fairness) == 
  IF TypeOK(cal)
  THEN 
    LET vars == cal.body @@ "VarDecl"
        procs == cal.body @@ "Proc"
        processes == cal.body @@ "Process"
        labels == cal.body @@ "Label"
        actions == [ action |-> << >>
                   ]
        Init == /\ vars @@ "Init"
                /\ procs @@ "Init"
                /\ processes @@ "Init"
        Next == 
          IF fairness = "none"
          THEN UNCHANGED << >>
          ELSEIF fairness = "weakPerAction"
          THEN [][Next]_<< >>
          ELSEIF fairness = "weakWholeNext"
          THEN WF_(Next, << >>)
          ELSEIF fairness = "strongPerAction"
          THEN SF_(Next, << >>)
        Spec == Init /\ [][Next]_<< >>
        Termination == << >>
    IN 
      vars @@ "Decl" 
      /\ procs @@ "Def"
      /\ processes @@ "Def"
      /\ labels @@ "Action"
      /\ actions @@ "Action"
      /\ Init
      /\ Next
      /\ Spec
      /\ Termination
  ELSE 
    "Invalid CAL algorithm"

=============================================================================