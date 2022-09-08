clean: ## Remove the not-checked-in generated files
	@rm -f *.aux *.dvi *.log *.ps *.pdf *.tex *.out *.dot

tlc:
	tlc -deadlock Example1_Simple
	tlc -deadlock Example2_Deadlock; test $$? -gt 0 # expect error here
	tlc -deadlock Example3_Parallel
	tlc -deadlock Example4_Choice
	tlc -deadlock Example5_MarkedGraph
	tlc -deadlock Example6_Bound
	tlc -deadlock Example7_ArcWeights
	tlc -deadlock Example8_Dining

tlatex:
	tlatex -shade PetriNet
	tlatex -shade Helpers
	tlatex -shade Example1_Simple
	tlatex -shade Example2_Deadlock
	tlatex -shade Example3_Parallel
	tlatex -shade Example4_Choice
	tlatex -shade Example5_MarkedGraph
	tlatex -shade Example6_Bound
	tlatex -shade Example7_ArcWeights
	tlatex -shade Example8_Dining

.PHONY: clean tlc tlatex
