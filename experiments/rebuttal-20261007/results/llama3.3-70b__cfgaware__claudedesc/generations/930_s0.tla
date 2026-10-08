```
MODULE HourClock
VARIABLE hr

HCini == (hr \in 1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

HC == HCini /\ [][HCnxt]_hr

THEOREM HC => []HCini
```
Note: The `_hr` subscript in the `HC` definition indicates that `hr` is the only variable that can change from one state to the next. This allows TLC to check the specification more efficiently by avoiding unnecessary exploration of states where other variables might change, even though there are no other variables in this simple example.