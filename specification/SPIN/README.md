
## Run verification

```
cd specification/SPIN
spin -a leader_election.pml
gcc pan.c -o pan
./pan
```

## Run simulation

```
cd specification/SPIN
spin leader_election.pml
```


## How to add a scenario

Add an `if` branch in the `init` proctype.
Specify a `ecpected_leader` and expected `Timeout`.

For example, if you want to add `link 0-2 and link 0-3 crash`, add the following:
```
:: 1 == 1 ->
        // example x: link 0-2 and link 0-3 crash
        expected_leader = 1;
        network[0]!Timeout(2, 0, 0);
        network[0]!Timeout(3, 0, 0);
        network[2]!Timeout(0, 0, 0);
        network[3]!Timeout(0, 0, 0);
```