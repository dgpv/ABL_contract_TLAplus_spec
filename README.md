# Specification for Asset-Based Lending smart contract

This repository contains the specification of the smart contract
for Asset-Based Lending that can be implemented on the blockchain
platform that uses UTXO model, if the platform has the capabilities
for expressive enough covenants.

## Specification in prose

Can be found in `ABL-spec-prose.pdf` file in this repository.

Describes the contract in English language

## TLA+ Specification

Can be found in `ABL_with_partial_repayments.tla`.

Implements the specification in TLA+ specification language.

Default values for constants can be found in `MC.tla`

To run `TLC` on the spec via included Makefile instead of
TLA+ toolbox in unix-like environment, you need `tla2tools.jar`
from https://github.com/tlaplus/tlaplus/releases or your local
TLA+ toolbox installation.

Set environment variable `TLATOOLSDIR` to the path where
`tla2tools.jar` is located.

Make sure you have `java` in your `PATH`

run `make` to apply `TLC` checker

run `make pdf` to generate PDF file for the TLA+ specification
(you need pdflatex to be in your `PATH` for that)


