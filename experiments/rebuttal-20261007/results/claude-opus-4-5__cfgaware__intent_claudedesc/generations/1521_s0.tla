---------------------------- MODULE CoffeeCan ----------------------------

EXTENDS Naturals

CONSTANTS MaxBeans

VARIABLES black, white, done

vars == <<black, white, done>>

TypeOK ==
    /\ black \in 0..MaxBeans
    /\ white \in 0..MaxBeans
    /\ black + white <= MaxBeans
    /\ done \in BOOLEAN

Init ==
    /\ black \in 0..MaxBeans
    /\ white \in 0..MaxBeans
    /\ black + white >= 1
    /\ black + white <= MaxBeans
    /\ done = FALSE

TotalBeans == black + white

\* Both beans are black: discard both, return one black (net: -1 black)
PickTwoBlack ==
    /\ ~done
    /\ black >= 2
    /\ black' = black - 1
    /\ white' = white
    /\ done' = (black' + white' = 1)

\* Both beans are white: discard both, add one black (net: -2 white, +1 black)
PickTwoWhite ==
    /\ ~done
    /\ white >= 2
    /\ black' = black + 1
    /\ white' = white - 2
    /\ done' = (black' + white' = 1)

\* One of each: return white, discard black (net: -1 black)
PickOneOfEach ==
    /\ ~done
    /\ black >= 1
    /\ white >= 1
    /\ black' = black - 1
    /\ white' = white
    /\ done' = (black' + white' = 1)

Terminating ==
    /\ done
    /\ UNCHANGED vars

Next ==
    \/ PickTwoBlack
    \/ PickTwoWhite
    \/ PickOneOfEach
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Property 1: Every non-stuttering step strictly decreases the total number of beans
\* We check this as an invariant on transitions
DecreasesTotal ==
    [][done \/ (black' + white' = black + white - 1)]_vars

\* Property 2: The parity of white beans is preserved (key loop invariant)
\* We express this as: white mod 2 is unchanged in every step
ParityPreserved ==
    [][white' % 2 = white % 2]_vars

\* Property 3: The process eventually terminates with exactly one bean
EventuallyTerminates ==
    <>(done /\ TotalBeans = 1)

\* Property 4: Terminal color is determined by initial white parity
\* If initial white count is even, final bean is black (black=1, white=0)
\* If initial white count is odd, final bean is white (black=0, white=1)
\* Since parity is preserved, we check: at termination, white=1 iff white%2=1
TerminalColorCorrect ==
    [](done => ((white % 2 = 0 => (black = 1 /\ white = 0)) /\
                (white % 2 = 1 => (black = 0 /\ white = 1))))

=========================================================================