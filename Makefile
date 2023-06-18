clean: ## Remove the generated files. only *.pdf files are checked in
	@rm -f docs/*.aux docs/*.dvi docs/*.log docs/*.ps docs/*.pdf docs/*.tex docs/*.out docs/*.dot

tlc:
	tlc -deadlock Example1_Simple
	tlc -deadlock Example2_Deadlock; test $$? -gt 0 # expect error here
	tlc -deadlock Example3_Parallel
	tlc -deadlock Example4_Choice
	tlc -deadlock Example5_MarkedGraph
	tlc -deadlock Example6_Bound
	tlc -deadlock Example7_ArcWeights
	tlc -deadlock Example8_Dining
	# Workflow Nets
	tlc -deadlock WFNet_Example.tla

tlatex:
	tlatex -shade -latexCommand "pdflatex" -latexOutputExt "pdf" -metadir "docs" PetriNet
	tlatex -shade -latexCommand "pdflatex" -latexOutputExt "pdf" -metadir "docs" Helpers
	tlatex -shade -latexCommand "pdflatex" -latexOutputExt "pdf" -metadir "docs" Example1_Simple
	tlatex -shade -latexCommand "pdflatex" -latexOutputExt "pdf" -metadir "docs" Example2_Deadlock
	tlatex -shade -latexCommand "pdflatex" -latexOutputExt "pdf" -metadir "docs" Example3_Parallel
	tlatex -shade -latexCommand "pdflatex" -latexOutputExt "pdf" -metadir "docs" Example4_Choice
	tlatex -shade -latexCommand "pdflatex" -latexOutputExt "pdf" -metadir "docs" Example5_MarkedGraph
	tlatex -shade -latexCommand "pdflatex" -latexOutputExt "pdf" -metadir "docs" Example6_Bound
	tlatex -shade -latexCommand "pdflatex" -latexOutputExt "pdf" -metadir "docs" Example7_ArcWeights
	tlatex -shade -latexCommand "pdflatex" -latexOutputExt "pdf" -metadir "docs" Example8_Dining
	# Workflow Nets
	tlatex -shade -latexCommand "pdflatex" -latexOutputExt "pdf" -metadir "docs" WFNet
	tlatex -shade -latexCommand "pdflatex" -latexOutputExt "pdf" -metadir "docs" WFNet_Example
	# tlatex keeps around the pdf files in the root even though metadir is set...
	rm *.pdf

.PHONY: clean tlc tlatex
