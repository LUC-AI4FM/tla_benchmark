------------------------------ MODULE InitStateGenerator ------------------------------
(***************************************************************************)
(* Model of an initialization generator for a single integer-valued state *)
(* variable x.  Given a finite list of initialization predicates (Boolean  *)
(* formulas built from equalities, conjunctions, disjunctions and the      *)
(* constants TRUE/FALSE), the generator enumerates every legal initial     *)
(* value of x, emitting each legal value exactly once.                     *)
(*                                                                         *)
(* Formula representation (records):                                       *)
(*   [kind |-> "TRUE"]                        constant tautology           *)
(*   [kind |-> "FALSE"]                       constant contradiction       *)
(*   [kind |-> "EqVarConst",  c  |-> n]       x = n                        *)
(*   [kind |-> "EqConstVar",  c  |-> n]       n = x                        *)
(*   [kind |-> "EqConstConst", c1 |-> a, c2 |-> b]   a = b                 *)
(*   [kind |-> "EqVarVar"]                    x = x                        *)
(*   [kind |-> "And", args |-> <<f1,...,fk>>] f1 /\ ... /\ fk              *)
(*   [kind |-> "Or",  args |-> <<f1,...,fk>>] f1 \/ ... \/ fk              *)
(*                                                                         *)
(* Predicates are evaluated semantically (by satisfiability under a given *)
(* value), so the order of evaluation of subexpressions, and the order in *)
(* which predicates are tried, cannot change the result.  The order in    *)
(* which candidate values and predicates are tried is nondeterministic.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Domain,     \* finite set of integers: candidate values of the state variable
    Preds       \* finite sequence of initialization predicates (formulas)

ASSUME DomainAssumption == IsFiniteSet(Domain) /\ Domain \subseteq Int
ASSUME PredsAssumption  == Preds \in Seq(UNION {Preds[i] : i \in 1..Len(Preds)} \cup {Preds[i] : i \in 1..Len(Preds)})
                           \/ Len(Preds) \in Nat

PredIdx == 1..Len(Preds)

(***************************************************************************)
(* Semantic evaluation of a formula under the assignment x = v.            *)
(***************************************************************************)
RECURSIVE Eval(_, _)
Eval(f, v) ==
    CASE f.kind = "TRUE"         -> TRUE
      [] f.kind = "FALSE"        -> FALSE
      [] f.kind = "EqVarConst"   -> v = f.c
      [] f.kind = "EqConstVar"   -> f.c = v
      [] f.kind = "EqConstConst" -> f.c1 = f.c2
      [] f.kind = "EqVarVar"     -> TRUE
      [] f.kind = "And"          -> \A k \in 1..Len(f.args) : Eval(f.args[k], v)
      [] f.kind = "Or"           -> \E k \in 1..Len(f.args) : Eval(f.args[k], v)

\* Set of values a single predicate accepts
AcceptedBy(i) == {v \in Domain : Eval(Preds[i], v)}

\* A value is legal iff at least one predicate is true under it
Legal(v) == \E i \in PredIdx : Eval(Preds[i], v)

\* The specification of the expected result
LegalSet == {v \in Domain : Legal(v)}

IsTautology(i)    == \A v \in Domain : Eval(Preds[i], v)
IsContradiction(i) == \A v \in Domain : ~Eval(Preds[i], v)

VARIABLES
    pending,    \* pending[v] : predicates not yet tried for candidate v
    produced,   \* set of initial states generated so far
    emitted,    \* sequence of emitted values (to detect duplicates)
    done        \* generator has terminated

vars == <<pending, produced, emitted, done>>

Range(s) == {s[k] : k \in 1..Len(s)}

TypeOK ==
    /\ pending \in [Domain -> SUBSET PredIdx]
    /\ produced \subseteq Domain
    /\ emitted \in Seq(Domain)
    /\ done \in BOOLEAN

Init ==
    /\ pending  = [v \in Domain |-> PredIdx]
    /\ produced = {}
    /\ emitted  = <<>>
    /\ done     = FALSE

(***************************************************************************)
(* Try predicate i on candidate value v (any order).  If satisfied, v is   *)
(* emitted once and no further predicates are tried for v.  Otherwise the *)
(* predicate is discarded for v.                                           *)
(***************************************************************************)
TryPred(v, i) ==
    /\ ~done
    /\ v \notin produced
    /\ i \in pending[v]
    /\ IF Eval(Preds[i], v)
         THEN /\ produced' = produced \cup {v}
              /\ emitted'  = Append(emitted, v)
              /\ pending'  = [pending EXCEPT ![v] = {}]
         ELSE /\ pending'  = [pending EXCEPT ![v] = @ \ {i}]
              /\ UNCHANGED <<produced, emitted>>
    /\ UNCHANGED done

Finish ==
    /\ ~done
    /\ \A v \in Domain : pending[v] = {}
    /\ done' = TRUE
    /\ UNCHANGED <<pending, produced, emitted>>

Terminated ==
    /\ done
    /\ UNCHANGED vars

Next ==
    \/ \E v \in Domain, i \in PredIdx : TryPred(v, i)
    \/ Finish
    \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(*************************** Safety properties ****************************)

\* No value is emitted more than once
NoDuplicates ==
    \A j, k \in 1..Len(emitted) : j # k => emitted[j] # emitted[k]

\* The produced set is exactly the set of emitted values
EmittedMatchesProduced ==
    /\ Range(emitted) = produced
    /\ Len(emitted) = Cardinality(produced)

\* Only legal values are ever produced
Soundness == produced \subseteq LegalSet

\* A value is only discarded after every predicate was found false for it
NoSpuriousOmission ==
    \A v \in Domain :
        v \notin produced =>
            \A i \in PredIdx \ pending[v] : ~Eval(Preds[i], v)

\* On termination, the produced set equals {v | \E p : p(v) = TRUE}
Correctness == done => produced = LegalSet

\* Tautologies accept all values; contradictions accept none
TautologyHandling ==
    \A i \in PredIdx : IsTautology(i) => (done => Domain \subseteq produced)

ContradictionHandling ==
    \A i \in PredIdx : IsContradiction(i) => AcceptedBy(i) = {}

\* The legal set is the union of per-predicate accepted sets
UnionCharacterization ==
    LegalSet = UNION {AcceptedBy(i) : i \in PredIdx}

SafetyInvariant ==
    /\ TypeOK
    /\ NoDuplicates
    /\ EmittedMatchesProduced
    /\ Soundness
    /\ NoSpuriousOmission
    /\ Correctness
    /\ TautologyHandling
    /\ ContradictionHandling
    /\ UnionCharacterization

(*************************** Liveness properties **************************)

\* Every legal value is eventually enumerated
EventuallyEnumeratesAll == \A v \in LegalSet : <>(v \in produced)

\* The generator eventually terminates with exactly the legal set
EventuallyComplete == <>[](done /\ produced = LegalSet)

Termination == <>done

THEOREM Spec => []SafetyInvariant
THEOREM Spec => (EventuallyEnumeratesAll /\ EventuallyComplete /\ Termination)
=============================================================================