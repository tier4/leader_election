cmake_minimum_required(VERSION 3.8)
project(converter)

find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)
find_package(autoware_adapi_v1_msgs REQUIRED)

add_executable(converter src/converter.cpp)
ament_target_dependencies(converter rclcpp autoware_adapi_v1_msgs)

install(TARGETS converter
  DESTINATION lib/${PROJECT_NAME})

ament_package()
