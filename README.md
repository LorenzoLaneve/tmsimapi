## A Non-Deterministic Turing Machine Simulator
###### Project of Algorithms and Data Structures (AY 2017/18, Politecnico di Milano)

The program simply takes an input file with the definition of a Turing Machine and some input strings, and simulates the normal functioning of a Turing Machine. The definition may provide non-deterministic moves.
The input file may be passed through the first argument from the shell. If not specified, standard input will be assumed. 

Here is the format for an input file:
```
tr
<transitions>
acc
<accepting-states>
max
<limit>
run
<strings>
```

The states of the Turing Machine are specified as integers (state IDs), with `0` being the initial state.

`<transitions>` consists of a list of transitions separated by a line feed. A single transition is specified as a tuple of 5 elements separated by white spaces. For example:
```
0 a b R 4
```
This means that from state `0`, reading `a`, the machine will write `b` and move the head to the `R`ight, reaching the state 4.
Possible values for the movement of the head are `L`eft, `R`ight, and `S`tay.

`<accepting-states>` will provide a sequence of integers separated by a line feed which are the IDs of the accepting states of the machine.

`<limit>` is a single integer (long integer) which is the maximum number of steps after which the machine will halt.

`<strings>` are a list of strings separated by a line feed that will be given as input to the Turing Machine defined by the first three clauses. There is not limit to the length of these strings.


The output will be a sequence of `n` outcomes separated by a line feed, with `n` the number of the strings specified in the input.
- `1` will indicate that the Turing Machine accepted the string;
- `0` will indicate that the Turing Machine rejected the string, and no branch of the computation reached the `<limit>`;
- `U` will indicate that the Turing Machine reached the `<limit>` in at least one branch of the computation and couldn't determine the outcome.
