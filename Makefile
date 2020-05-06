NAME = ABL_with_partial_repayments
PROSE_NAME = ABL-spec-prose

all: build/metadir
	java -jar ${TLATOOLSDIR}/tla2tools.jar \
	    -config ${NAME}.cfg \
	    -workers 1 \
	    -metadir metadir \
	    -terse \
	    -cleanup \
	    -deadlock \
	    MC.tla

pdf: build/metadir
	java -cp ${TLATOOLSDIR}/tla2tools.jar tla2tex.TLA \
	    -metadir metadir \
	    -latexOutputExt pdf \
	    -latexCommand pdflatex \
	    -ptSize 12 \
	    -shade \
	    ${NAME}.tla

prose: build
	rst2html5.py --math-output="MathJax ${MATHJAX_URL}" ${PROSE_NAME}.rst > build/${PROSE_NAME}.html

clean:
	rm -rf build

build:
	mkdir -p build

build/metadir:
	mkdir -p build/metadir
