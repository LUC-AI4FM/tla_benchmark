---------------------------- MODULE Quicksort ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat \ {0}

PermsOf(Arr) ==
  LET Automorphisms(D) == { f \in [D -> D] : \A y \in D : \E x \in D : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphisms(DOMAIN Arr) }

(***************************************************************************
--algorithm Quicksort {
  variables Ainit \in [1..N -> 1..N] ; A = Ainit ;
            S = {<<1, N>>} ; pivot = 1 ;

  macro Partition(lo, hi) {
    with (piv \in lo..(hi-1)) {
      pivot := piv ;
      with (Ap \in {AA \in PermsOf(A) :
                      (\A i \in (1..(lo-1)) \cup ((hi+1)..N) : AA[i] = A[i])
                      /\ \A i \in lo..piv, j \in (piv+1)..hi : AA[i] \leq AA[j]}) {
        A := Ap
      } ;
      S := (S \ {<<lo, hi>>}) \cup {<<lo, piv>>, <<piv+1, hi>>}
    }
  }

  { qs1: while (S # {}) {
           with (I \in S) {
             if (I[1] < I[2]) { Partition(I[1], I[2]) }
             else { S := S \ {I} }
           }
         }
  }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES Ainit, A, S, pivot, pc

vars == << Ainit, A, S, pivot, pc >>

Init == /\ Ainit \in [1..N -> 1..N]
        /\ A = Ainit
        /\ S = {<<1, N>>}
        /\ pivot = 1
        /\ pc = "qs1"

qs1 == /\ pc = "qs1"
       /\ IF S # {}
             THEN /\ \E I \in S :
                       IF I[1] < I[2]
                          THEN /\ \E piv \in I[1]..(I[2]-1) :
                                    /\ pivot' = piv
                                    /\ \E Ap \in {AA \in PermsOf(A) :
                                                    (\A i \in (1..(I[1]-1)) \cup ((I[2]+1)..N) :
                                                         AA[i] = A[i])
                                                    /\ \A i \in I[1]..piv, j \in (piv+1)..I[2] :
                                                         AA[i] \leq AA[j]} :
                                          A' = Ap
                                    /\ S' = (S \ {I}) \cup {<<I[1], piv>>, <<piv+1, I[2]>>}
                          ELSE /\ S' = S \ {I}
                               /\ UNCHANGED << A, pivot >>
                  /\ pc' = "qs1"
             ELSE /\ pc' = "Done"
                  /\ UNCHANGED << A, S, pivot >>
       /\ Ainit' = Ainit

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == qs1 \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

TypeOK == /\ Ainit \in [1..N -> 1..N]
          /\ A \in [1..N -> 1..N]
          /\ pivot \in 1..N
          /\ pc \in {"qs1", "Done"}
=============================================================================