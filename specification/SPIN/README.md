
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
