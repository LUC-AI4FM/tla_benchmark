MODULE Github715
VARIABLE x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_{x}

Prop  == [](x)

Prop2 == (x = TRUE)

Prop3 == TRUE

SpecVar == x