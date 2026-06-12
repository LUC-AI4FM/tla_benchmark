MODULE PrintUtility

EXTENDS Integers, TLC

CONSTANTS 
    x, y, z

VARIABLES 
    rec

Init == rec = [a |-> 0, b |-> 1]

Next == /\ rec' = [rec EXCEPT !.a = rec.a + 1]
        /\ rec'.b = rec.b * 2

PrintVal(id, val) == <<id, val>>

ASSUME 
    LET 
        a_val == rec.a
        b_val == rec.b
        sum_val == a_val + b_val
        product_val == a_val * b_val
        expr1 == x + y
        expr2 == z - x
        expr3 == y * z
    IN
        /\ Print(PrintVal("a", a_val))
        /\ Print(PrintVal("b", b_val))
        /\ Print(PrintVal("sum of a and b", sum_val))
        /\ Print(PrintVal("product of a and b", product_val))
        /\ Print(PrintVal("x + y", expr1))
        /\ Print(PrintVal("z - x", expr2))
        /\ Print(PrintVal("y * z", expr3))

Spec == Init /\ [][Next]_<<rec>>