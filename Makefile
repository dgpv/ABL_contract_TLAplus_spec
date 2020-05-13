NAME = ABL_with_partial_repayments
PROSE_NAME = ABL-spec-prose

all: prose

check: build/metadir
	java -jar ${TLATOOLSDIR}/tla2tools.jar \
	    -config ${NAME}.cfg \
	    -workers 1 \
	    -metadir build/metadir \
	    -terse \
	    -cleanup \
	    -deadlock \
	    MC.tla

pdf: build/metadir
	java -cp ${TLATOOLSDIR}/tla2tools.jar tla2tex.TLA \
	    -metadir build/metadir \
	    -latexOutputExt pdf \
	    -latexCommand pdflatex \
	    -ptSize 12 \
	    -shade \
	    ${NAME}.tla

prose: build/${PROSE_NAME}.html

build/${PROSE_NAME}.html: ${PROSE_NAME}.rst  build
	rst2html5.py --math-output="MathJax ${MATHJAX_URL}" ${PROSE_NAME}.rst > build/${PROSE_NAME}.html

clean:
	rm -rf build

build:
	mkdir -p build
	ln -s ../images/ build/images

build/metadir:
	mkdir -p build/metadir

.PHONY: all check pdf prose clean
