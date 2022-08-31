# petri-tlaplus 🕸️

TLA+ module for [Petri Nets](https://en.wikipedia.org/wiki/Petri_net). Petri Nets are a simple and natural abstraction for modeling stepwise processes, concurrency, and stateful distributed systems.

Instantiate the `PetriNet` module to model a specific graph and assert temporal properties about all its possible executions!

## Try it

Install the [TLA+ tools](https://lamport.azurewebsites.net/tla/standalone-tools.html). I install them with Nix by running `nix-shell -p tlaplus`.

```
# Model check Petri Nets.
tlc -deadlock Example1_Simple
tlc -deadlock Example3_Parallel

# Read pretty-printed specifications (.ps files).
tlatex -shade PetriNet           # the core module
tlatex -shade Example1_Simple
tlatex -shade Example3_Parallel

# Visualize the state graph using graphviz (*.dot files).
tlc -deadlock Example6_Bound -dump dot out

# Check all specification via make targets
make tlc       # model check all examples
make tlatex    # pretty-print all modules
make clean
```

See `PetriNet.tla` for the core module. See the `Example_*.tla`/`Example_*.cfg` files for usage and an introduction to some Petri net concepts.
