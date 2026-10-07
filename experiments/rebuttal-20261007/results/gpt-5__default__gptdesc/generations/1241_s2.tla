------------------------------ MODULE PlusCal_Translator ------------------------------

EXTENDS Naturals, Sequences

(*
  Executable TLA+ specification of a translator from a PlusCal (+CAL) global-naming
  abstract syntax tree (AST) to a TLA+ lexeme sequence, including Init, Next, Spec,
  and a Termination property in the generated text. It also models fairness options
  for the generated specification: None, WF on process actions, WF on Next, SF on
  process actions.

  The dynamic state machine below produces the lexeme sequence by consuming a TODO
  stack of AST nodes. Liveness (Termination) is guaranteed under weak fairness of
  the Step action.
*)

CONSTANTS
  ASTInput,          \* an AST node representing a top-level algorithm (root tag "Alg")
  FairnessMode       \* one of {"None","WFProc","WFNext","SFProc"}

ASSUME FairnessMode \in {"None","WFProc","WFNext","SFProc"}

(*
  Inductively generated set of AST nodes (uniform record shape).
  Each node is a record: [tag: Tags, name: STRING, text: STRING, children: Seq(Node)]
  We define it by height-bounded approximations Nodes(k) and take the union over k.
*)

Tags == {
  "Alg", "Proc", "Process",
  "Labeled", "Assign", "If", "While", "Either", "With",
  "Call", "Return", "Skip", "Assert", "Var", "Stmt", "Body"
}

RECURSIVE Nodes(_)

Nodes(k) ==
  IF k = 0 THEN
    { [tag |-> t, name |-> n, text |-> tx, children |-> <<>>] :
        t \in Tags /\ n \in STRING /\ tx \in STRING }
  ELSE
    LET Sub == UNION { Nodes(j) : j \in 0..(k-1) }
    IN
    { [tag |-> t, name |-> n, text |-> tx, children |-> cs] :
        t \in Tags /\ n \in STRING /\ tx \in STRING /\ cs \in Seq(Sub) }

NodeSet == UNION { Nodes(k) : k \in Nat }

(*
  Grammar predicates for convenience. These are simple tag checks plus NodeSet membership.
  Finer-grained structural constraints (e.g., child tag patterns) can be added as needed.
*)

IsAlg(n) == n \in NodeSet /\ n.tag = "Alg"
IsProc(n) == n \in NodeSet /\ n.tag = "Proc"
IsProcess(n) == n \in NodeSet /\ n.tag = "Process"
IsStmt(n) == n \in NodeSet /\ n.tag \in {"Labeled","Assign","If","While","Either","With","Call","Return","Skip","Assert","Stmt","Body","Var"}

SeqToSet(s) == { s[i] : i \in 1..Len(s) }

ChildrenTags(n) == [i \in 1..Len(n.children) |-> n.children[i].tag]

(*
  Translation to lexeme sequences (strings). These are pure operators that compute
  sequences of tokens (strings) representing TLA+ text.

  Emit traverses the AST and assembles a flat sequence of lexemes. For "Alg" nodes
  it emits a mock module header, basic definitions for Init/Next/Spec, and a
  Termination property, then emits the translation of children.
*)

RECURSIVE Emit(_), EmitList(_), GenInitLex(_), GenNextLex(_), GenSpecLex(_, _), GenTerminationLex(_)

Emit(n) ==
  CASE n.tag = "Alg" ->
         (<<"----", "MODULE", n.name, "----">>
          \o <<"EXTENDS", "Naturals", "Sequences">>
          \o <<"VARIABLES", "vars">>
          \o GenInitLex(n)
          \o GenNextLex(n)
          \o GenSpecLex(n, FairnessMode)
          \o GenTerminationLex(n)
          \o EmitList(n.children)
          \o <<"====