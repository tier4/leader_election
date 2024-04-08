## ROS 2 implementation

### build
```
$ source /opt/ros/humble/setup.bash
$ cd implementations/ros2
$ colcon build
```

### run
```
$ cd implementations/ros2
$ source install/setup.bash
$ ros2 launch launch/leader_election.xml
```

### node crash
```
$ cd implementations/ros2
# in terminal1
$ source install/setup.bash
$ ros2 launch launch/leader_election.xml

# in terminal2
$ source install/setup.bash
$ ros2 topic pub --once /{ecu_name}/shutdown std_msgs/msg/Empty {}
```

### link crash
```
$ cd implementations/ros2
# in terminal1
$ source install/setup.bash
$ ros2 launch launch/leader_election.xml

# in terminal2
$ source install/setup.bash
$ ros2 topic pub --once /{ecu_name1}/to/{ecu_names2}/link_crash std_msgs/msg/Empty {}
$ ros2 topic pub --once /{ecu_name2}/to/{ecu_names1}/link_crash std_msgs/msg/Empty {}
```