
# Run

## Run verification

```
cd specification/SPIN
make run
```

## Run error trail

```
cd specification/SPIN
make trail
```


# Change verification scenarios

## Change verification scenario with 4 nodes

1. delete the existing scenario in `init` process
```
    // invoke a node 0 crash in 4 nodes
    // crash[0] = true;
    // expected_leader = 1;
    // network[1].interface[0]!Timeout(0, 0); // 0 means nothing
    // network[2].interface[0]!Timeout(0, 0); // 0 means nothing
    // network[3].interface[0]!Timeout(0, 0); // 0 means nothing
```

2. add a new scenario
```
    // invoke a link 0-1 crash in 4 nodes
    expected_leader = 2;
    network[1].interface[0]!Timeout(0, 0); // 0 means nothing
    network[0].interface[1]!Timeout(0, 0); // 0 means nothing
```

## Change verification scenario with more than 4 nodes

1. change `NODE_NUM`
```
// #define NODE_NUM 4
#define NODE_NUM 5
```

2. change termination check
```
// termination on 4 nodes
// #define finished_election ( \
//     (crash[0] || (empty(network[0].interface[1]) && empty(network[0].interface[2]) && empty(network[0].interface[3]))) && \
//     (crash[1] || (empty(network[1].interface[0]) && empty(network[1].interface[2]) && empty(network[1].interface[3]))) && \
//     (crash[2] || (empty(network[2].interface[0]) && empty(network[2].interface[1]) && empty(network[2].interface[3]))) && \
//     (crash[3] || (empty(network[3].interface[0]) && empty(network[3].interface[1]) && empty(network[3].interface[2]))) \
// )

// termination on 5 nodes
#define finished_election ( \
    (crash[0] || (empty(network[0].interface[1]) && empty(network[0].interface[2]) && empty(network[0].interface[3]) && empty(network[0].interface[4]))) && \
    (crash[1] || (empty(network[1].interface[0]) && empty(network[1].interface[2]) && empty(network[1].interface[3]) && empty(network[0].interface[4]))) && \
    (crash[2] || (empty(network[2].interface[0]) && empty(network[2].interface[1]) && empty(network[2].interface[3]) && empty(network[0].interface[4]))) && \
    (crash[3] || (empty(network[3].interface[0]) && empty(network[3].interface[1]) && empty(network[3].interface[2]) && empty(network[0].interface[4]))) && \
    (crash[4] || (empty(network[4].interface[0]) && empty(network[4].interface[1]) && empty(network[4].interface[2]) && empty(network[4].interface[3]))) \
)
```

3. replace scenario in `init` process
```
    // invoke a node 0 crash in 4 nodes
    // crash[0] = true;
    // expected_leader = 1;
    // network[1].interface[0]!Timeout(0, 0); // 0 means nothing
    // network[2].interface[0]!Timeout(0, 0); // 0 means nothing
    // network[3].interface[0]!Timeout(0, 0); // 0 means nothing

    // invoke a node 0 crash in 5 nodes
    // crash[0] = true;
    // expected_leader = 1;
    network[1].interface[0]!Timeout(0, 0); // 0 means nothing
    network[2].interface[0]!Timeout(0, 0); // 0 means nothing
    network[3].interface[0]!Timeout(0, 0); // 0 means nothing
    network[4].interface[0]!Timeout(0, 0); // 0 means nothing
```
