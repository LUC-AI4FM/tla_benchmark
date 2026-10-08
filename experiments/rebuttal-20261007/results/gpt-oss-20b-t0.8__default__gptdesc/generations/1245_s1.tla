MODULE PlusCal2TLA
EXTENDS Naturals, Sequences

CONSTANT FairnessOption \in {"None", "WeakProc", "WeakNext", "StrongProc"}

VARIABLES ast, state, pc

(****************************************************************************)
(*  Abstract syntax tree grammar (placeholders)                               *)
(****************************************************************************)

Node == [type : STRING, fields : SUBSET (ANY -> ANY)]

Expr == Node
Stmt == Node

IsExpr[n] == n.type = "expr"
IsStmt[n] == n.type = "stmt"

(****************************************************************************)
(*  Translation pipeline functions (identity placeholders)                   *)
(****************************************************************************)

Explode[ast_]    == ast                     \* explode structured statements
TranslateCalls[ast_] == ast                 \* translate calls, returns, gotos
AddSubs[ast_, pid_] == ast                  \* add subscripts for process local vars

(****************************************************************************)
(*  Specification building functions (placeholders)                          *)
(****************************************************************************)

BuildInit[ast_] ==
   /\ state = [v |-> 0]                \* initial state placeholder

BuildNext[ast_] ==
   \E i \in Nat : TRUE                 \* next-state relation placeholder

Safe[s_] == TRUE                        \* safety invariant placeholder

Termination ==
   []~(BuildNext[Explode[TranslateCalls[AddSubs[ast, 0]]]])

(****************************************************************************)
(*  Initial state and Next relation                                          *)
(****************************************************************************)

Init == BuildInit[Explode[TranslateCalls[AddSubs[ast, 0]]]]

Next == BuildNext[Explode[TranslateCalls[AddSubs[ast, 0]]]]

SafetyInvariant == \A s \in DOMAIN state : Safe[s]

(****************************************************************************)
(*  Fairness conditions                                                      *)
(****************************************************************************)

WeakFair[act_] == WF_vars(act_)
StrongFair[act_] == SF_vars(act_)

FairnessCondition ==
   CASE
     FairnessOption = "None"      => TRUE
   \/ FairnessOption = "WeakProc" => WeakFair[BuildNext[Explode[TranslateCalls[AddSubs[ast, 0]]]]]
   \/ FairnessOption = "WeakNext" => WF_vars(Next)
   \/ FairnessOption = "StrongProc"=> StrongFair[BuildNext[Explode[TranslateCalls[AddSubs[ast, 0]]]]]

(****************************************************************************)
(*  Final specification                                                      *)
(****************************************************************************)

Spec == Init
        /\ [][Next]_vars
        /\ SafetyInvariant
        /\ FairnessCondition

===============================================================================