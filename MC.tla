---- MODULE MC ----
EXTENDS ABL_with_partial_repayments, TLC

const_P == 10000
const_N == 4
const_M == 2
const_RateDue == 200
const_RateEarly == 10
const_RatesLate == <<300, 550>>
const_BLOCKS_IN_PERIOD == 4

=============================================================================
