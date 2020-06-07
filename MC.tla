---- MODULE MC ----
EXTENDS ABL_with_partial_repayments, TLC, Logging

const_P == 10000
const_C == 100000
const_N == 4
const_M == 4
const_RateDue == 200
const_RateEarly == 10
const_RateCollateralPenalty == 1000
const_RatesLate == <<300, 550, 800>>
\* const_RatesLate == <<300, 550>>
const_S == Max({const_N, const_M})+1
\* const_S == const_N + const_M
const_BLOCKS_IN_PERIOD == 4
const_START_BLOCK == 1


=============================================================================
