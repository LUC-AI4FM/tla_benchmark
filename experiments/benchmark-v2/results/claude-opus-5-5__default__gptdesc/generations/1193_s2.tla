------------------------------- MODULE PrimeTest -------------------------------
(***************************************************************************)
(* Regression-style test specification for the handling of primed         *)
(* expressions in many syntactic contexts inside the next-state relation. *)
(* The state space is tiny: x and y start at 1, the first step sets x to  *)
(* 2, and every later step leaves the state unchanged.  Therefore exactly *)
(* two distinct states are reachable: [x = 1, y = 1] and [x = 2, y = 1].  *)
(*                                                                         *)
(* Every check is wrapped in TLC's Assert, so any inconsistent evaluation *)
(* of x' makes model checking fail with an error.                          *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

(***************************************************************************)
(* Helper operators used to test primed arguments and primed bodies.       *)
(***************************************************************************)
Inc(a)       == a + 1
Plus(a, b)   == a + b
PrimedX      == x'
PrimedXPlus1 == x' + 1
IsTwo(a)     == a = 2

(***************************************************************************)
(* Initial predicate.                                                      *)
(***************************************************************************)
Init == /\ x = 1
        /\ y = 1

(***************************************************************************)
(* Next-state relation.  x' is fixed first, then it is used in many        *)
(* different syntactic contexts, each of which must agree on x' = 2.       *)
(***************************************************************************)
Next ==
  /\ x' = 2
  /\ y' = y
  /\ PrintT(<<"x' =", x'>>)
  \* Plain comparison
  /\ Assert(x' = 2, "Failure: plain x'")
  \* Function definitions involving x'
  /\ LET f[i \in {1, 2}] == x' + i
     IN  /\ Assert(f[1] = 3, "Failure: function definition (1)")
         /\ Assert(f[2] = 4, "Failure: function definition (2)")
  /\ LET g == [i \in {1, 2} |-> x' * i]
     IN  Assert(g = <<2, 4>>, "Failure: function constructor")
  \* Set expressions involving x'
  /\ Assert({x'} = {2}, "Failure: set enumeration")
  /\ Assert({i \in {1, 2, 3} : i = x'} = {2}, "Failure: set filter")
  /\ Assert({x' + i : i \in {0, 1}} = {2, 3}, "Failure: set map")
  /\ Assert(x' \in {1, 2}, "Failure: set membership")
  /\ Assert(x' \notin {1, 3}, "Failure: set non-membership")
  /\ Assert(SUBSET {x'} = {{}, {2}}, "Failure: SUBSET")
  /\ Assert(({x'} \cup {y'}) = {1, 2}, "Failure: set union")
  \* CHOOSE involving x'
  /\ Assert((CHOOSE i \in {1, 2, 3} : i = x') = 2, "Failure: CHOOSE")
  /\ Assert((CHOOSE i \in {x'} : TRUE) = 2, "Failure: CHOOSE over {x'}")
  \* Function override (EXCEPT) involving x'
  /\ LET h == [i \in {1, 2} |-> 0]
     IN  /\ Assert([h EXCEPT ![1] = x'] = <<2, 0>>,
                   "Failure: EXCEPT value")
         /\ Assert([h EXCEPT ![x'] = 7] = <<0, 7>>,
                   "Failure: EXCEPT index")
         /\ Assert([h EXCEPT ![1] = @ + x'] = <<2, 0>>,
                   "Failure: EXCEPT with @")
  \* CASE involving x'
  /\ Assert(CASE x' = 1 -> FALSE
              [] x' = 2 -> TRUE
              [] OTHER  -> FALSE,
            "Failure: CASE")
  /\ Assert((CASE x' = 2 -> x' + 1 [] OTHER -> 0) = 3, "Failure: CASE value")
  \* IF-THEN-ELSE involving x'
  /\ Assert(IF x' = 2 THEN TRUE ELSE FALSE, "Failure: IF-THEN-ELSE")
  \* Quantifiers involving x'
  /\ Assert(\E i \in {1, 2, 3} : i = x', "Failure: bounded exists")
  /\ Assert(\A i \in {x'} : i = 2, "Failure: bounded forall")
  /\ Assert(\A i \in {1} : i + 1 = x', "Failure: forall body")
  /\ Assert(~ \E i \in {1, 3} : i = x', "Failure: negated exists")
  \* Implication / equivalence involving x'
  /\ Assert(x' = 2 => TRUE, "Failure: implication (antecedent)")
  /\ Assert(TRUE => x' = 2, "Failure: implication (consequent)")
  /\ Assert(x' = 1 => FALSE, "Failure: vacuous implication")
  /\ Assert((x' = 2) <=> (y' = 1), "Failure: equivalence")
  \* Operator calls involving x'
  /\ Assert(Inc(x') = 3, "Failure: operator argument")
  /\ Assert(Plus(x', y') = 3, "Failure: two primed arguments")
  /\ Assert(PrimedX = 2, "Failure: operator with primed body")
  /\ Assert(PrimedXPlus1 = 3, "Failure: operator with primed expression")
  /\ Assert(IsTwo(x'), "Failure: Boolean operator call")
  /\ Assert(Inc(PrimedX) = 3, "Failure: nested operator calls")
  \* LET involving x'
  /\ LET z == x' + y'
     IN  Assert(z = 3, "Failure: LET")
  \* Tuples and records involving x'
  /\ Assert(<<x', y'>> = <<2, 1>>, "Failure: tuple")
  /\ Assert([a |-> x', b |-> y'].a = 2, "Failure: record")

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety invariants.                                                      *)
(***************************************************************************)
TypeOK == /\ x \in {1, 2}
          /\ y = 1

\* Only two distinct states are reachable.
TwoStates == <<x, y>> \in {<<1, 1>>, <<2, 1>>}

(***************************************************************************)
(* Liveness: eventually x becomes 2 and stays there.                       *)
(***************************************************************************)
EventuallyTwo == <>[](x = 2)

THEOREM Spec => [](TypeOK /\ TwoStates)
=============================================================================