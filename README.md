# petri-tlaplus 🕸️

TLA+ module for [Petri Nets](https://en.wikipedia.org/wiki/Petri_net). Petri Nets are a simple and natural abstraction for modeling stepwise processes, concurrency, and stateful distributed systems.

Instantiate the `PetriNet` module to model a specific graph and assert temporal properties about all its possible executions!

## Try it

Install the [TLA+ tools](https://lamport.azurewebsites.net/tla/standalone-tools.html). I install them with Nix by running `nix-shell -p tlaplus`.

```
# Model check Petri Nets.
tlc -deadlock Example1_Simple
tlc -deadlock Example3_Parallel

# Generate LaTeX PDF docs. See the `docs/` dir
tlatex -shade -latexCommand "pdflatex" -latexOutputExt "pdf" -metadir "docs" PetriNet

# Visualize the state graph using graphviz (*.dot files).
tlc -deadlock Example6_Bound -dump dot Example6_Bound

# Check all specification via make targets
make tlc       # model check all modules
make tlatex    # pretty-print all modules to `docs/`
make clean     # delete all generated files
```

See `PetriNet.tla` for the core module. See the `Example_*.tla`/`Example_*.cfg` files for usage and an introduction to some Petri net concepts.

## Petri Net Specification

Excerpts of the constant and variable definitions and the core "Fire" action. See [`docs/PetriNet.pdf`](https://github.com/elh/petri-tlaplus/blob/main/docs/PetriNet.pdf) and [`docs/`](https://github.com/elh/petri-tlaplus/tree/main/docs) dir for the full LaTeX pretty-printed specification and more examples.

<p align="center">
    <img src="https://github.com/elh/petri-tlaplus/assets/1035393/9785d20e-8be7-47e7-b9ff-eb892384b1c3">
</p>
<p align="center">
    <img src="https://github.com/elh/petri-tlaplus/assets/1035393/1474a3d6-13d2-4934-80d0-7195b7245fd4">
</p>

Note that the "Workflow net" specifications are incomplete due to a limitation of the TLA+ model checker.
