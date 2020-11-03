---------------------- MODULE ABL_with_partial_repayments ----------------------
(******************************************************************************)
(* Copyright (C) 2020 Dmitry Petukhov https://github.com/dgpv                 *)
(******************************************************************************)

(******************************************************************************)
(* This specification encodes the description given in prose in the file      *)
(* ``ABL-spec-prose.rst`` and some of the one-letter names for the constants  *)
(* and variables are as the same as used in the prose description.            *)
(* Only the behavor after the start of the contract is specified here.        *)
(* For example, "Bob has received P" is implied.                              *)
(******************************************************************************)

(******************************************************************************)
(* Note that due to limitations of model checker that only supports 32-bit    *)
(* signed integer numbers, the calculations of the amounts might not be exact *)
(* due to the rounding inherent in integer calculations                       *)
(******************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC

Min(set) == CHOOSE x \in set: \A y \in set : x <= y
Max(set) == CHOOSE x \in set: \A y \in set : x >= y

\* Rate 1.51% with RATE_PRECISION=10000 will be represented as 151
RATE_PRECISION == 10000

\* Note that C (the collateral amount) is not defined because
\* in this contract the amount of collateral does not change

\* The amount of the Principal asset
CONSTANT P
ASSUME P > 0
\* The amount of the Collateral asset
CONSTANT C
ASSUME C > 0
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
\* `^\newpage^'
\* The rate for surcharge on early repayments
CONSTANT RateEarly
ASSUME RateEarly <= RATE_PRECISION
\* The rates for surcharge on late repayment
CONSTANT RatesLate
ASSUME DOMAIN RatesLate = 1..M-1
ASSUME \A x \in DOMAIN RatesLate: RatesLate[x] <= RATE_PRECISION
\* The maximum number of steps in the contract
CONSTANT RateCollateralPenalty
ASSUME RateCollateralPenalty <= RATE_PRECISION
CONSTANT S
ASSUME S \in Max({N, M})+1..(N+M)
\* The duration of each time period in blocks. S periods is the
\* max duration of the contract (assuming TimelyEnforcement)
CONSTANT BLOCKS_IN_PERIOD
\* Included to make the algorithm closer to the real world,
\* where the contract starts at arbitray block. Can be arbitrary Nat value.
CONSTANT START_BLOCK

CONSTANT C_UNCOND
ASSUME C_UNCOND <= C

VARIABLES block, state

fullState == <<block, state>>

ApplyRate(v, r) == (v * r) \div RATE_PRECISION

ApplyLateRate(v, rn) == IF rn = 0 THEN 0 ELSE ApplyRate(v, RatesLate[rn])

P_remainder == P % N

\* The Principal amount is assumed to be much larger than number of periods
ASSUME N < P \div 100

\* Include the remainder in the last payment
LimitByBalance(v) == IF v + P_remainder >= state.B THEN state.B ELSE v

\* `^\newpage^'
\* "Fraction of P" is the installment size
FracP == (P \div N)

\* D is the portion of the balance currently due
D == LimitByBalance(FracP * (state.m + 1))

\* L is the amount the repayment is late on
L == LimitByBalance(FracP * state.m)

\* When TimelyEnforcement is in effect, the value returned by PeriodOf
\* corresponds to 's' in the prose description
PeriodOf(b) == (b - START_BLOCK) \div BLOCKS_IN_PERIOD

StepsTaken == Len(state.path)

InDefault(m, period) == m >= M \/ period >= S-1

RegularRepaymentAmount == D + ApplyRate(state.B, RateDue) + ApplyLateRate(L, state.m)

RegularRepayment ==
    state' = [n |-> state.n + 1,
              m |-> 0,
              B |-> state.B - D,
              total_repaid |-> state.total_repaid + RegularRepaymentAmount,
              path |-> state.path \o ">",
              at_block |-> block,
              custody |-> IF state.B = D THEN [Debtor_R |-> C] ELSE state.custody]

EarlyRepaymentAmount ==
    state.B + ApplyRate(state.B, RateDue)
            + ApplyRate((state.B-D), RateEarly)
            + ApplyLateRate(LimitByBalance(FracP * state.m),
                            state.m)

\* `^\newpage^'
EarlyRepayment ==
    state' = [state EXCEPT !.B = 0,
                           !.total_repaid = state.total_repaid
                                            + EarlyRepaymentAmount,
                           !.path = state.path \o "!",
                           !.custody = [Debtor_E |-> C]]

Repayment ==
    \/ RegularRepayment
    \/ /\ EarlyRepaymentAmount > RegularRepaymentAmount
       /\ EarlyRepayment

AmountForCollateralForfeiturePenalty ==
    Max({ state.B, RegularRepaymentAmount })
    + ApplyRate(Max({ state.B, RegularRepaymentAmount }),
                RateCollateralPenalty)

RepaymentMissed ==
    IF InDefault(state.m + 1, PeriodOf(block))
    THEN LET C_forfeited ==
                Max({ C_UNCOND,
                      Min({ C, (C * AmountForCollateralForfeiturePenalty)
                               \div P }) })
          IN state' = [state
                       EXCEPT !.m = state.m + 1,
                              !.path = state.path \o "X",
                              !.custody = [Creditor |-> C_forfeited,
                                           Debtor_D |-> C - C_forfeited]]
    ELSE state' = [state
                   EXCEPT !.m = state.m + 1,
                          !.at_block = block,
                          !.path = state.path \o "v"]


\* `^\newpage^'
\* If it is possible that nothing happens within a period,
\* the number of states to check grows while all that new states
\* will be duplicates. It can be said that no action within a period
\* just means that period is now 2x as long, but the overal state
\* of the contract does not progress.
NoIdlePeriods == PeriodOf(block) <= PeriodOf(state.at_block) + 1

Enforcement ==
    \* More than one repayment can happen on a single period,
    \* but extra repayments do cover the subsequent periods,
    \* so we cannot use state.at_block and need to use
    \* for this check the number of steps taken
    IF PeriodOf(block) > StepsTaken
    THEN RepaymentMissed
    ELSE UNCHANGED state

\* `^\newpage^'
(***************)
(* Invariants  *)
(***************)

TypeOK ==
    /\ DOMAIN state = {"n", "m", "B", "at_block", "total_repaid", "custody",
                       "path"}
    /\ state.n \in 0..N
    /\ state.m \in 0..M
    /\ LET cdom == DOMAIN state.custody
        IN IF "Creditor" \notin cdom
           THEN /\ Cardinality(cdom) = 1
                /\ cdom \subseteq {"Contract", "Debtor_R", "Debtor_E"}
           ELSE cdom = {"Creditor", "Debtor_D"}
    /\ StepsTaken <= N * M

ConsistentProgress ==
    IF "Contract" \in DOMAIN state.custody
    THEN
        \* Early repayment available only before N-1 steps are taken
        /\ IF StepsTaken < N-1
           THEN EarlyRepaymentAmount > RegularRepaymentAmount
           ELSE EarlyRepaymentAmount = RegularRepaymentAmount
    ELSE TRUE

ConsistentRepayment ==
    IF DOMAIN state.custody \intersect {"Debtor_R", "Debtor_E"} /= {}
    THEN state.B = 0 /\ state.total_repaid >= P
    ELSE TRUE

ConsistentEnforcement ==
    NoIdlePeriods /\ PeriodOf(block) > 0
    => (InDefault(state.m, PeriodOf(block) - 1)
        => /\ "Creditor" \in DOMAIN state.custody
           /\ state.custody["Creditor"] + state.custody["Debtor_D"] = C
           /\ (state.total_repaid = 0 => state.custody["Creditor"] = C))

ConsistentRemainder ==
    (state.B >= FracP \/ state.B = 0) \* last payment includes P_remainder

ConsistentPeriods ==
    NoIdlePeriods
    => \* At least one step in each period has to be taken
       \* when enforcement is on-time
       /\ PeriodOf(block) <= StepsTaken + 1
       \* Can progress over S time periods, period index in 0..S-1
       /\ PeriodOf(block) <= S

(***************)
(* Init & Next *)
(***************)

Init ==
    /\ block = START_BLOCK
    /\ state = [n |-> 0, m |-> 0, B |-> P, at_block |-> block,
                total_repaid |-> 0, path |-> "", custody |-> [Contract |-> C]]

Next ==
    /\ DOMAIN state.custody = {"Contract"}
    /\ NoIdlePeriods
    /\ \/ Repayment          /\ UNCHANGED block
       \/ Enforcement        /\ UNCHANGED block
       \/ block' = block + 1 /\ UNCHANGED state

Spec == Init /\ [][Next]_fullState

================================================================================
