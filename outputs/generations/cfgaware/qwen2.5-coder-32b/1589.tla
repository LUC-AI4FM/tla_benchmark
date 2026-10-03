------------------------------- MODULE EuclidGCD -------------------------------

CONSTANTS MaxNum

VARIABLES pc, u_ini, v_ini, u, v

(*--algorithm EuclidGCD
variables u = u_ini, v = v_ini;
begin
    while (u /= v) do
        if (u > v)
            then u := u - v;
            else v := v - u;
end algorithm *)

\* BEGIN TRANSLATION
Spec == 
  /\ pc \in {"Init", "WhileCond", "IfThen", "Else", "Done"}
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u \in 0..MaxNum
  /\ v \in 0..MaxNum
  /\ (pc = "Init" => <<u, v>> = <<u_ini, v_ini>>)
  /\ (pc # "Init" => <<u, v>> \in [1..MaxNum] \X [1..MaxNum])
  /\ WF_pc(Next)

Init == 
  pc = "Init"

WhileCond ==
  \/ /\ pc = "Init"
     /\ u /= v
     /\ pc' = "WhileCond"
  \/ /\ pc = "WhileCond"
     /\ u = v
     /\ pc' = "Done"
  \/ /\ pc = "IfThen" 
     /\ u > v
     /\ pc' = "WhileCond"
  \/ /\ pc = "Else"
     /\ u <= v
     /\ pc' = "WhileCond"

IfThen ==
  /\ pc = "WhileCond"
  /\ u > v
  /\ u' = u - v
  /\ v' = v
  /\ pc' = "IfThen"

Else ==
  /\ pc = "WhileCond"
  /\ u <= v
  /\ u' = u
  /\ v' = v - u
  /\ pc' = "Else"

Done ==
  /\ pc = "WhileCond"
  /\ u = v
  /\ pc' = "Done"

Next == WhileCond \/ IfThen \/ Else

WF_pc(action) == 
  \A state \in StateSpace : 
    EnabledIn(state, action) => 
      \E state' \in StateSpace : 
        action /\ ['][pc'] = state'[pc] /\ state' \notin BoundedStates

EnabledIn(state, action) ==
  LET pcVal == state[pc]
      uVal == state[u]
      vVal == state[v]
  IN
    \/ /\ pcVal = "Init"
       /\ action = Init
    \/ /\ pcVal = "WhileCond"
       /\ action \in {WhileCond, IfThen, Else}
    \/ /\ pcVal \in {"IfThen", "Else"}
       /\ action = WhileCond

StateSpace == 
  { <<pcVal, u_iniVal, v_iniVal, uVal, vVal>> \in [1..5 -> S] :
      pcVal \in {"Init", "WhileCond", "IfThen", "Else", "Done"} /\
      u_iniVal \in 1..MaxNum /\
      v_iniVal \in 1..MaxNum /\
      uVal \in 0..MaxNum /\
      vVal \in 0..MaxNum }

BoundedStates ==
  { <<pcVal, _, _, uVal, vVal>> \in StateSpace :
      pcVal = "Done" /\ uVal = vVal }

GCD(a, b) == 
  LET rec_gcd(x, y) ==
    IF x = y THEN x
    ELSE IF x > y THEN rec_gcd(x - y, y)
         ELSE rec_gcd(x, y - x)
  IN
    rec_gcd(a, b)

Termination ==
  <>(pc = "Done")

Invariant ==
  /\ pc \in {"Init", "WhileCond", "IfThen", "Else", "Done"}
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u \in 0..MaxNum
  /\ v \in 0..MaxNum
  /\ (pc = "Init" => <<u, v>> = <<u_ini, v_ini>>)
  /\ (pc # "Init" => GCD(u_ini, v_ini) = GCD(u, v))

\* END TRANSLATION

=============================================================================