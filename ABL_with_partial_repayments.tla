---------------------- MODULE ABL_with_partial_repayments ----------------------
(******************************************************************************)
(* Copyright (C) 2020 Dmitry Petukhov https://github.com/dgpv                 *)
(******************************************************************************)

(******************************************************************************)
(* This specification is encodes the specification given in prose in the file *)
(* ABL-spec-prose.rst and some of the one-letter names for the constants      *)
(* and variables are as the same as in the prose specification.               *)
(* Only the behavor after the start of the contract is specified here.        *)
(* For example, "Bob has received P" is implied.                              *)
(******************************************************************************)

(******************************************************************************)
(* It is natural to model the asset amounts as Natural numbers because in the *)
(* on-chain contract they are represented in satoshis                         *)
(******************************************************************************)

EXTENDS Naturals, Sequences, TLC

Min(x, y) == IF x < y THEN x ELSE y
Max(x, y) == IF x > y THEN x ELSE y

\* Rate 1.51% with RATE_PRECISION=10000 will be represented as 151
RATE_PRECISION == 10000

\* Note that C (the collateral amount) is not defined because
\* in this contract the amount of collateral does not change

\* The amount of the Principal asset
CONSTANT P
ASSUME P > 0
\* The number of installments the full repayment is split into
CONSTANT N
ASSUME N > 0
\* The number consecutive missed payments that result
\* in collateral forfeiture.
CONSTANT M
ASSUME M > 0
\* The rate for regular repayments due
CONSTANT RateDue
ASSUME RateDue <= RATE_PRECISION
\* The rate for surcharge on early repayments
CONSTANT RateEarly
ASSUME RateEarly <= RATE_PRECISION
\* The rates for surcharge on late repayment
CONSTANT RatesLate
ASSUME DOMAIN RatesLate = 1..M-1
ASSUME \A x \in DOMAIN RatesLate: RatesLate[x] <= RATE_PRECISION
\* The minumum number of steps in the contract
CONSTANT S_min
ASSUME S_min \in Min(N, M)..(N+M)
\* The maximum number of steps in the contract
CONSTANT S_max
ASSUME S_max \in Max(N, M)..(N+M)
\* The duration of each time period in blocks. S_max periods is the
\* max duration of the contract (assuming TimelyEnforcement)
CONSTANT BLOCKS_IN_PERIOD
\* Included to make the algorithm closer to the real world,
\* where the contract starts at arbitray block. Can be arbitrary Nat value.
CONSTANT START_BLOCK

VARIABLES block, state

fullState == <<block, state>>

ApplyRate(v, r) == (v * r) \div RATE_PRECISION

ApplyLateRate(v, rn) == IF rn = 0 THEN 0 ELSE ApplyRate(v, RatesLate[rn])

P_remainder == P % N

\* The Principal amount is assumed to be much larger than number of periods
ASSUME P_remainder < P \div 100

\* Include the remainder in the last payment
LimitByBalance(v) == IF v + P_remainder >= state.B THEN state.B ELSE v

\* "Fraction of P" is the installment size
FracP == (P \div N)

\* D is the portion of the balance currently due
D == LimitByBalance(FracP * (state.m + 1))

\* L is the amount the repayment is late on
L == LimitByBalance(FracP * state.m)

\* When TimelyEnforcement is in effect, the value returned by PeriodOf
\* corresponds to 's' in the prose spec
PeriodOf(b) == (b - START_BLOCK) \div BLOCKS_IN_PERIOD

StepsTaken == Len(state.path)

InDefault(m, period) == m >= M \/ period >= S_max

RegularRepaymentAmount == D + ApplyRate(D, RateDue) + ApplyLateRate(L, state.m)

RegularRepayment ==
    state' = [n |-> state.n + 1,
              m |-> 0,
              B |-> state.B - D,
              total_repaid |-> state.total_repaid + RegularRepaymentAmount,
              path |-> state.path \o ">",
              at_block |-> block,
              custody |-> IF state.B = D THEN "Debtor>" ELSE state.custody]

EarlyRepaymentAmount ==
    state.B + ApplyRate(D, RateDue)
            + ApplyRate((state.B-D), RateEarly)
            + ApplyLateRate(LimitByBalance(FracP * state.m),
                            state.m)

EarlyRepayment ==
    state' = [state EXCEPT !.B = 0,
                           !.total_repaid = state.total_repaid
                                            + EarlyRepaymentAmount,
                           !.path = state.path \o "!",
                           !.custody = "Debtor!"]

Repayment ==
    /\ ~InDefault(state.m, PeriodOf(block))
    /\ \/ RegularRepayment
       \/ /\ EarlyRepaymentAmount > RegularRepaymentAmount
          /\ EarlyRepayment

RepaymentMissed ==
    IF InDefault(state.m + 1, PeriodOf(block))
    THEN state' = [state EXCEPT !.m = state.m + 1,
                                !.path = state.path \o "X",
                                !.custody = "Creditor"]
    ELSE state' = [state EXCEPT !.m = state.m + 1,
                                !.at_block = block,
                                !.path = state.path \o "v"]

Enforcement ==
    IF PeriodOf(block) /= PeriodOf(state.at_block)
    THEN RepaymentMissed
    ELSE UNCHANGED state

\* If the enforcement is not done in time, the number of states to check grows
\* while all that new states will be duplicates. It can be said that
\* no enforcement within the period just means that period is now 2x as long,
\* but the overal state of the contract does not progress.
\* No-enforcement only hurts the Creditor, and it is the Creditor who is
\* doing the enforcement, so there's natural incentive for them to enforce.
TimelyEnforcement == PeriodOf(block) <= PeriodOf(state.at_block) + 1

(***************)
(* Invariants  *)
(***************)

TypeOK ==
    /\ DOMAIN state = {"n", "m", "B", "at_block", "total_repaid", "custody",
                       "path"}
    /\ state.n \in 0..N
    /\ state.m \in 0..M
    /\ state.custody \in {"Contract", "Debtor>", "Debtor!", "Creditor"}
    /\ StepsTaken <= N * M

ConsistentProgress ==
    IF state.custody = "Contract"
    THEN
        \* Early repayment available only before N-1 steps are taken
        /\ IF StepsTaken < N-1
           THEN EarlyRepaymentAmount > RegularRepaymentAmount
           ELSE EarlyRepaymentAmount = RegularRepaymentAmount
    ELSE TRUE


ConsistentRepayment ==
    IF state.custody \in {"Debtor>", "Debtor!"}
    THEN /\ state.B = 0
         /\ state.total_repaid >= P
         /\ ~InDefault(state.m, PeriodOf(block))
    ELSE TRUE

ConsistentEnforcement ==
    IF state.custody = "Creditor" 
    THEN InDefault(state.m, PeriodOf(block))
    ELSE TRUE

ConsistentRemainder ==
    (state.B >= FracP \/ state.B = 0) \* last payment includes P_remainder

ConsistentPeriods ==
    IF TimelyEnforcement
    THEN
        \* At least one step in each period has to be taken
        \* when enforcement is on-time
        /\ PeriodOf(block) <= StepsTaken + 1
        \* Can progress over S_max + 1 time periods, period index in 0..S_max
        /\ PeriodOf(block) <= S_max
    ELSE TRUE

(***************)
(* Init & Next *)
(***************)

Init ==
    /\ block = START_BLOCK
    /\ state = [n |-> 0, m |-> 0, B |-> P, at_block |-> block,
                total_repaid |-> 0, path |-> "", custody |-> "Contract"]

Next ==
    /\ state.custody = "Contract"
    /\ TimelyEnforcement
    /\ \/ Repayment          /\ UNCHANGED block
       \/ Enforcement        /\ UNCHANGED block
       \/ block' = block + 1 /\ UNCHANGED state

Spec == Init /\ [][Next]_fullState

================================================================================
