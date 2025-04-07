all: user-manual.pdf

user-manual.pdf: *.tex images/*.png
	latexmk -shell-escape -pdf user-manual.tex

clean: 
	rm -f user-manual.pdf user-manual.log user-manual.fdb_latexmk user-manual.aux user-manual.toc user-manual.fls