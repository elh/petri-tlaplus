# petri-tlaplus

TLA+ modules and specifications for [Petri Nets](https://en.wikipedia.org/wiki/Petri_net).

## Try it

Install the [TLA+ tools](https://lamport.azurewebsites.net/tla/standalone-tools.html).

```
# model check a simple, example Petri Net.
tlc -deadlock Example1
tlc -deadlock Example3

# read pretty printed specifications (*.ps files).
tlatex -shade PetriNet
tlatex -shade Example1
tlatex -shade Example3
```

🕸️
