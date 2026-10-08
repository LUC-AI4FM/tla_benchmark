MODULE ASTTranslator

EXTENDS Naturals, Sequences

CONSTANTS AlgAST, FairnessOption

VARIABLES seq, pos

(* --- Translation operator ------------------------------------------- *)

Translate(a) == {"Init", "Next", "Spec", "Termination"}

(* --- Actions -------------------------------------------------------- *)

ProcessAction ==
  [pos' = pos + 1 ∧ pos < Len(seq)]

Next == ProcessAction

(* --- Initialisation ----------------------------------------------- *)

Init ==
  /\ seq = Translate(AlgAST)
  /\ pos = 0

(* --- Safety invariants -------------------------------------------- *)

Invariant1 == pos <= Len(seq)

(* --- Liveness property --------------------------------------------- *)

Termination == <> (pos = Len(seq))

(* --- Specification with fairness options --------------------------- *)

Spec ==
  IF FairnessOption = "NoFairness" THEN
      Init /\ [][Next] /\ Invariant1
  ELSEIF FairnessOption = "WeakFairnessProc" THEN
      Init /\ WEAK_FAIRNESS ProcessAction /\ [][Next] /\ Invariant1
  ELSEIF FairnessOption = "StrongFairnessProc" THEN
      Init /\ STRONG_FAIRNESS ProcessAction /\ [][Next] /\ Invariant1
  ELSE
      Init /\ WEAK_FAIRNESS Next /\ [][Next] /\ Invariant1

(* --- Theorem ------------------------------------------------------ *)

THEOREM Spec => Termination

===============================================================================