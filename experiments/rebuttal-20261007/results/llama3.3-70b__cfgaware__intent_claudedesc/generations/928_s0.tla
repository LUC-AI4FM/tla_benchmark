```
EXTENDS HourClock

VARIABLE hour

HC == hour \in 1..12

NextHour(hour) == 
  IF hour = 12 THEN 1 ELSE hour + 1

NextHourMod(hour) == (hour mod 12) + 1

HC2 == HC /\ [][NextHourMod(hour)]_hour
```