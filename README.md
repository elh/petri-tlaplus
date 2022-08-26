# petri-tlaplus 🕸️

TLA+ module for [Petri Nets](https://en.wikipedia.org/wiki/Petri_net). Petri Nets are a simple and natural abstraction for modelling stepwise processes, concurrency, and stateful distributed systems.

Instantiate the `PetriNet` module to model a specific graph and assert temporal properties about all its possible executions!

## Try it

Install the [TLA+ tools](https://lamport.azurewebsites.net/tla/standalone-tools.html).

```
# Model check Petri Nets.
tlc -deadlock Example1_Simple
tlc -deadlock Example3_Parallel

# Read pretty-printed specifications (.ps files).
tlatex -shade PetriNet           # the core module
tlatex -shade Example1_Simple
tlatex -shade Example3_Parallel
```
