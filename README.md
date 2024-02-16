# leader_election

## prototype

### build
```
$ source /opt/ros/humble/setup.bash
$ cd demo
$ colcon build
```

### run
```
$ cd demo
$ source install/setup.bash
$ ros2 launch launch/leader_election.xml
```

### node crash
```
$ cd demo
# in terminal1
$ source install/setup.bash
$ ros2 launch launch/leader_election.xml

# in terminal2
$ source install/setup.bash
$ ros2 topic pub --once /{ecu_name}/shutdown std_msgs/msg/Empty {}
```

### link crash
```
$ cd demo
# in terminal1
$ source install/setup.bash
$ ros2 launch launch/leader_election.xml

# in terminal2
$ source install/setup.bash
$ ros2 topic pub --once /{ecu_name1}/to/{ecu_names2}/link_crash std_msgs/msg/Empty {}
$ ros2 topic pub --once /{ecu_name2}/to/{ecu_names1}/link_crash std_msgs/msg/Empty {}
```