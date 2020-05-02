NAME = ABL_with_partial_repayments

all: metadir
	java -jar ${TLATOOLSDIR}/tla2tools.jar \
	    -config ${NAME}.cfg \
	    -workers 1 \
	    -metadir metadir \
	    -terse \
	    -cleanup \
	    -deadlock \
	    MC.tla

pdf: metadir
	java -cp ${TLATOOLSDIR}/tla2tools.jar tla2tex.TLA \
	    -metadir metadir \
	    -latexOutputExt pdf \
	    -latexCommand pdflatex \
	    -ptSize 12 \
	    -shade \
	    ${NAME}.tla

clean:
	rm -rf metadir

metadir:
	mkdir -p metadir
