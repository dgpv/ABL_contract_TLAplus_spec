# Specification for Asset-Based Lending smart contract

This repository contains the specification of the smart contract
for Asset-Based Lending that can be implemented on the blockchain
platform that uses UTXO model, if the platform has the capabilities
for expressive enough covenants.

## Description in prose

Aims to describe the contract in a way that links the requirements
(what participants want to achieve) with the specification
(how the contract makes that possible)

Can be found in `ABL-spec-prose.pdf`

The source in Restructured Text is in `ABL-spec-prose.rst`

## Specification in [TLA+](https://lamport.azurewebsites.net/tla/tla.html)

Can be found in `ABL_with_partial_repayments.tla`, specifies the
variant with partial repayments.

This is a high-level specification, it does not specify the details
how the restrictions required for the contract are implemented
on the particular blockchain platform

Default values for constants can be found in `MC.tla`

`ABL_with_partial_repayments.pdf` is the spec rendered with `make pdf`

## Rendering the prose spec

To generate html from `ABL-spec-prose.rst`, you neeed:

[rst2html5.py](https://docutils.sourceforge.io/docs/user/tools.html#rst2html5-py)
from the docutils package.

For math symbol rendering, [MathJax](https://www.mathjax.org/) is used.

The generation command needs `MATHJAX_URL` environment variable to be set
to the the url of the MathJax.js file (can be a local `file://` url if you are
generating the file for local-only viewing).

To generate the html, run:

run `make prose`

The `ABL-spec-prose.pdf` in this repository is generated by printing the
html file to pdf file from the browser.

Alternatively, any other ways to convert `.rst` file to the rendered
document can be used, but the quality of results may vary.

## Working with TLA spec from command line

To run `TLC` on the spec via included Makefile instead of
TLA+ toolbox in unix-like environment, you need `tla2tools.jar`
from https://github.com/tlaplus/tlaplus/releases or your local
TLA+ toolbox installation.

Set environment variable `TLATOOLSDIR` to the path where
`tla2tools.jar` is located.

Make sure you have `java` in your `PATH`

run `make check` to apply `TLC` checker

run `make pdf` to generate PDF file for the TLA+ specification
(you need pdflatex to be in your `PATH` for that)

## Authors and contributors

The contract specification is designed by Dmitry Petukhov

With review and help from Russell O'Connor
