------------------------------- MODULE PCR_Cycle -------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxPrimers, MaxTemplates

VARIABLES temp, primers, dsDNA, ssTemplates, hybrids

Init == 
  /\ temp = 0
  /\ primers \in 0..MaxPrimers
  /\ dsDNA = 0
  /\ ssTemplates \in 0..MaxTemplates
  /\ hybrids = 0

Next ==
  \/ /\ temp = 95            (* Heating *)
     /\ primers' = primers
     /\ dsDNA' = dsDNA
     /\ ssTemplates' = ssTemplates
     /\ hybrids' = 0
     /\ UNCHANGED temp
  \/ /\ temp = 68            (* Cooling/Annealing *)
     /\ \/ /\ hybrids' \in 0..(MIN(primers, ssTemplates))
        /\ primers' = primers - hybrids'
        /\ dsDNA' = dsDNA
        /\ ssTemplates' = ssTemplates - hybrids'
        /\ temp' = 72
     \/ /\ hybrids' = hybrids
        /\ primers' = primers
        /\ dsDNA' = dsDNA
        /\ ssTemplates' = ssTemplates
        /\ temp' = 95
  \/ /\ temp = 72            (* Extension *)
     /\ hybrids' = 0
     /\ primers' = primers
     /\ dsDNA' = dsDNA + hybrids
     /\ ssTemplates' = ssTemplates
     /\ temp' = 68

Spec ==
  INIT Init
  /\ NEXT Next
  /\ WF_vars(<<temp, primers, dsDNA, ssTemplates, hybrids>>)

WF_vars(seq) == \/ seq = <<95, 0, 0, 0, 0>>
                \/ \E t1, p1, d1, s1, h1, t2, p2, d2, s2, h2 \in Int :
                   /\ <<t1, p1, d1, s1, h1>> \in seq
                   /\ <<t2, p2, d2, s2, h2>> \in seq
                   /\ t2 = 68 /\ (h2 < h1 \/ (h2 = 0 /\ t1 = 95))
                   /\ p2 \leq p1 /\ d2 >= d1 /\ s2 <= s1

(* Safety properties *)
InvPrimers == primers \in 0..MaxPrimers
InvTemplates == ssTemplates \in 0..MaxTemplates
InvHybrids == hybrids \in 0..MIN(primers, ssTemplates)
InvNonnegativity == /\ primers >= 0
                    /\ dsDNA >= 0
                    /\ ssTemplates >= 0
                    /\ hybrids >= 0
InvCountPreservation == primers + dsDNA + ssTemplates + hybrids = MaxPrimers + MaxTemplates

(* Liveness properties *)
PrimerDepletion == <>(primers = 0)

=============================================================================