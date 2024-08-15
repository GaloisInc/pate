all: user-manual.pdf

user-manual.pdf: *.tex images/*.png
	latexmk -shell-escape -pdf user-manual.tex
