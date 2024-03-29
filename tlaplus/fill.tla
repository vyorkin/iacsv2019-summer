---- MODULE fill ---------------------------------------------------------------

EXTENDS Integers

VARIABLES small, big

TypeOK == /\small \in 0..3
          /\big \in 0..5

Init == /\big = 0
        /\small = 0

FillSmall == /\small' = 3
             /\big' = big

FillBig == /\big' = 5
           /\small' = small

EmptySmall == /\small' = 0
              /\big' = big

EmptyBig == /\big' = 0
            /\small' = small

SmallToBigA == /\ big + small <= 5
               /\ big'   = big + small
               /\ small' = 0

SmallToBigB == /\ big + small > 5
               /\ big'   = 5
               /\ small' = small - (5 - big)

BigToSmallA == /\ big + small <= 3
               /\ small' = big + small
               /\ big'   = 5 - (big + small)

BigToSmallB == /\ big + small > 3
               /\ small' = 3
               /\ big'   = big + small - 3

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBigA
        \/ SmallToBigB
        \/ BigToSmallA
        \/ BigToSmallB

Mew == big /=4

================================================================================
