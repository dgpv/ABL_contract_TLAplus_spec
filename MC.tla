---- MODULE MC ----
EXTENDS ABL_with_partial_repayments, TLC, Logging

const_P == 10000
const_N == 4
const_M == 4
const_RateDue == 200
const_RateEarly == 10
const_RatesLate == <<300, 550, 750>>
const_S_min == Min(const_N, const_M)
const_S_max == Max(const_N, const_M)
const_BLOCKS_IN_PERIOD == 4
const_START_BLOCK == 1


=============================================================================
