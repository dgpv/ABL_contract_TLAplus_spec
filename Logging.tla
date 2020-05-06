------------------------------ MODULE Logging -------------------------------
EXTENDS ABL_with_partial_repayments, TLC

Logging ==
    \/ /\ state'.custody = "Contract"
       /\ StepsTaken = PeriodOf(block) \* ignore duplicates
       /\ state'.B /= state.B
       /\ Print(<<"RR ", \* "Regular repayment"
                  PeriodOf(block), state.n, state.m, state.path,
                  RegularRepaymentAmount>>, TRUE)
    \/ /\ state'.custody = "Debtor>"
       /\ StepsTaken = PeriodOf(block) \* ignore duplicates
       /\ Print(<<"RR_", \* "Regular repayment final"
                  PeriodOf(block), state.n, state.m, state.path,
                  RegularRepaymentAmount>>, TRUE)
    \/ /\ state'.custody = "Debtor!"
       /\ StepsTaken = PeriodOf(block) \* ignore duplicates
       /\ Print(<<"ER ", \* "Early repayment "
                  PeriodOf(block), state.n, state.m, state.path,
                  EarlyRepaymentAmount>>, TRUE)
    \/ /\ state'.custody = "Creditor"
       /\ Print(<<"CF ", \* Collateral forfeiture
                  PeriodOf(block), state.n, state.m, state.path,
                  state.total_repaid>>, TRUE)
    \/ TRUE

=============================================================================
