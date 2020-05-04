---------------------- MODULE ABL_with_partial_repayments ----------------------
(******************************************************************************)
(* Copyright (C) 2020 Dmitry Petukhov https://github.com/dgpv                 *)
(******************************************************************************)

(******************************************************************************)
(* Amounts are modeled as Naturals because in smart contract they will be     *)
(* represented in satoshis                                                    *)
(******************************************************************************)

EXTENDS Naturals, Sequences, TLC

\* Note that C (the collateral amount) is not defined because
\* with this algorithm the amount of collateral does not change
CONSTANTS P, N, M, RateDue, RateEarly, RatesLate, BLOCKS_IN_PERIOD

VARIABLES block, total_repaid, state

RATE_PRECISION == 10000
START_BLOCK == 1

ASSUME {P, N, M, BLOCKS_IN_PERIOD} \subseteq Nat
ASSUME \A x \in {RateDue, RateEarly}: x \in Nat /\ x <= RATE_PRECISION
ASSUME DOMAIN RatesLate = 1..M
ASSUME \A x \in DOMAIN RatesLate:
        RatesLate[x] \in Nat /\ RatesLate[x] <= RATE_PRECISION

ApplyRate(v, r) == (v * r) \div RATE_PRECISION
ApplyLateRate(v, rn) == IF rn = 0 THEN 0 ELSE ApplyRate(v, RatesLate[rn])

P_remainder == P % N

\* The Principal amount is assumed to be much larger than number of periods
ASSUME P_remainder < P \div 100

LimitByBalance(v) == IF v + P_remainder >= state.B THEN state.B ELSE v

FracP == (P \div N)
D == LimitByBalance(FracP * (state.m + 1))

fullState == <<block, state, total_repaid>>

PeriodOf(b) == (b - START_BLOCK) \div BLOCKS_IN_PERIOD

Init == /\ block = START_BLOCK
        /\ state = [n |-> 0, m |-> 0, B |-> P, at_block |-> block,
                    path |-> "", custody |-> "Contract"]
        /\ total_repaid = 0

RegularRepaymentAmount == D + ApplyRate(D, RateDue)
                            + ApplyLateRate(LimitByBalance(FracP * state.m),
                                            state.m)

RegularRepayment ==
   /\ total_repaid' = total_repaid + RegularRepaymentAmount
   /\ state' = [n |-> state.n + 1,
                m |-> 0,
                B |-> state.B - D,
                path |-> state.path \o ">",
                at_block |-> block,
                custody |-> IF state.B = D THEN "Debtor" ELSE state.custody]

   \* Path len = period when always only one transition per period happens
   \* Can use this code to generate the normal state transition table
   \*
   \* /\ IF Len(state.path) = PeriodOf(block)
   \*    THEN Print(<<"RR", PeriodOf(block), state.n, state.m, state.path,
   \*                  RegularRepaymentAmount>>, TRUE)
   \*    ELSE TRUE
    
EarlyRepaymentAmount == state.B + ApplyRate(D, RateDue)
                                + ApplyRate((state.B-D), RateEarly)
                                + ApplyLateRate(LimitByBalance(FracP * state.m),
                                                state.m)

EarlyRepayment ==
    /\ total_repaid' = total_repaid + EarlyRepaymentAmount
    /\ state' = [state EXCEPT !.B = 0,
                              !.path = state.path \o "!",
                              !.custody = "Debtor"]

    \* Path len = period when always only one transition per period happens
    \* Can use this code to generate the normal state transition table
    \*
    \* /\ IF Len(state.path) = PeriodOf(block)
    \*    THEN Print(<<"ER", PeriodOf(block), state.n, state.m, state.path,
    \*                 EarlyRepaymentAmount>>, TRUE)
    \*    ELSE TRUE

Enforcement ==
    IF PeriodOf(block) /= PeriodOf(state.at_block)
    THEN state' = [state EXCEPT !.m = state.m + 1,
                                !.at_block = block,
                                !.path = state.path \o "v",
                                !.custody = IF state.m + 1 > M
                                            THEN "Creditor"
                                            ELSE state.custody]
    ELSE UNCHANGED state

\* If the enforcement is not done in time, the number of states to check grows
\* while all that new states will be duplicates. It can be said that
\* no enforcement within the period just means that period is now 2x as long,
\* but the overal state of the contract does not progress.
\* No-enforcement only hurts the Creditor, and it is the Creditor who is
\* doing the enforcement, so there's natural incentive for them to enforce.
EnforcementIsOnTime == PeriodOf(block) <= PeriodOf(state.at_block) + 1

TypeOK == DOMAIN state = {"n", "m", "B", "at_block", "custody", "path"}

IsConsistent ==
    /\ (state.B = 0 \/ state.B >= FracP)
    /\ IF /\ Len(state.path) > M /\ state.custody = "Contract"
       THEN RegularRepaymentAmount = EarlyRepaymentAmount
       ELSE TRUE

Next == /\ state.custody = "Contract"
        /\ EnforcementIsOnTime
        /\ \/ RegularRepayment   /\ UNCHANGED block
           \/ EarlyRepayment     /\ UNCHANGED block
           \/ Enforcement        /\ UNCHANGED <<block, total_repaid>>
           \/ block' = block + 1 /\ UNCHANGED <<state, total_repaid>>

        \* For debugging
        \* /\ Print(<<block', state'>>, TRUE)

Spec == Init /\ [][Next]_fullState

================================================================================
