------------------------------ MODULE Logging -------------------------------
EXTENDS ABL_with_partial_repayments, TLC

LoggingVariants ==
    \/ /\ "Contract" \in DOMAIN state'.custody
       /\ state.B /= state'.B
       /\ Print(<<"RR", \* "Regular repayment"
                  PeriodOf(block'), state'.n, state'.m, state'.path, state'.B,
                  RegularRepaymentAmount, state'.total_repaid, state'.custody>>,
                  TRUE)
    \/ /\ "Debtor_R" \in DOMAIN state'.custody
       /\ Print(<<"RF", \* "Regular repayment final"
                  PeriodOf(block'), state'.n, state'.m, state'.path,
                  RegularRepaymentAmount, state'.total_repaid, state'.custody>>,
                  TRUE)
    \/ /\ "Debtor_E" \in DOMAIN state'.custody
       /\ Print(<<"ER", \* "Early repayment "
                  PeriodOf(block'), state'.n, state'.m, state'.path,
                  EarlyRepaymentAmount, state'.total_repaid, state'.custody>>,
                  TRUE)
    \/ /\ "Creditor" \in DOMAIN state'.custody
       /\ Print(<<"CF", \* Collateral forfeiture
                  PeriodOf(block'), state'.n, state'.m, state'.path,
                  RegularRepaymentAmount, AmountForCollateralForfeiturePenalty,
                  state'.total_repaid, state'.custody>>, TRUE)
Logging ==
    \/ /\ LoggingVariants
    \/ TRUE

=============================================================================
