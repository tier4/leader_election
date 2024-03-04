#include <chrono>
#include <functional>
#include <memory>
#include <vector>

#include "rclcpp/rclcpp.hpp"
#include "std_msgs/msg/empty.hpp"
#include "std_msgs/msg/int8.hpp"

using namespace std::chrono_literals;
using std::placeholders::_1;

class ECU : public rclcpp::Node
{
  public:
    ECU() : Node("ecu")
    {
      // parameters
      ecu_id = declare_parameter<int>("ecu_id");
      ecu_name = declare_parameter<std::string>("ecu_name");
      current_leader = declare_parameter<int>("current_leader", 0);
      timeout_threshold = declare_parameter<double>("timeout_threshold", 0.3);

      // variables
      ecu_num = 4;
      received_time = std::vector<rclcpp::Time>(ecu_num);
      is_connected = std::vector<bool>(ecu_num, false);
      ecu_names = std::vector<std::string>{"main_ecu", "sub_ecu", "main_vcu", "sub_vcu"};
      reply_counts = std::vector<int>(16);
      leader_votes = std::vector<int>(16);
      external_link_crash = std::vector<bool>(ecu_num, false);
      election_id_cycle = 4;

      // publishers
      publisher_heartbeats_ = std::vector<rclcpp::Publisher<std_msgs::msg::Int8>::SharedPtr>(4);
      publisher_elections_ = std::vector<rclcpp::Publisher<std_msgs::msg::Int8>::SharedPtr>(4);
      publisher_replys_ = std::vector<rclcpp::Publisher<std_msgs::msg::Int8>::SharedPtr>(4);
      publisher_leaders_ = std::vector<rclcpp::Publisher<std_msgs::msg::Int8>::SharedPtr>(4);
      for (int i = 0; i < ecu_num; i++) {
        if (i == ecu_id) continue;
        publisher_heartbeats_[i] = this->create_publisher<std_msgs::msg::Int8>(
          '/' + ecu_name + "/to/" + ecu_names[i] + "/heartbeat", 1);
        publisher_elections_[i] = this->create_publisher<std_msgs::msg::Int8>(
          '/' + ecu_name + "/to/" + ecu_names[i] + "/election", 1);
        publisher_replys_[i] = this->create_publisher<std_msgs::msg::Int8>(
          '/' + ecu_name + "/to/" + ecu_names[i] + "/reply", 1);
        publisher_leaders_[i] = this->create_publisher<std_msgs::msg::Int8>(
          '/' + ecu_name + "/to/" + ecu_names[i] + "/leader", 1);
      }

      // subscriptions
      subscription_heartbeats_ = std::vector<rclcpp::Subscription<std_msgs::msg::Int8>::SharedPtr>(4);
      subscription_elections_ = std::vector<rclcpp::Subscription<std_msgs::msg::Int8>::SharedPtr>(4);
      subscription_replys_ = std::vector<rclcpp::Subscription<std_msgs::msg::Int8>::SharedPtr>(4);
      subscription_leaders_ = std::vector<rclcpp::Subscription<std_msgs::msg::Int8>::SharedPtr>(4);
      for (int i = 0; i < ecu_num; i++) {
        if (i == ecu_id) continue;
        subscription_heartbeats_[i] = this->create_subscription<std_msgs::msg::Int8>(
          "/" + ecu_names[i] + "/to/" + ecu_name + "/heartbeat", 1, [this, i](const std_msgs::msg::Int8 msg) {this->onHeartbeat(msg, i);});
        subscription_elections_[i] = this->create_subscription<std_msgs::msg::Int8>(
          "/" + ecu_names[i] + "/to/" + ecu_name + "/election", 1, [this, i](const std_msgs::msg::Int8 msg) {this->onElection(msg, i);});
        subscription_replys_[i] = this->create_subscription<std_msgs::msg::Int8>(
          "/" + ecu_names[i] + "/to/" + ecu_name + "/reply", 1, std::bind(&ECU::onReply, this, _1));
        subscription_leaders_[i] = this->create_subscription<std_msgs::msg::Int8>(
          "/" + ecu_names[i] + "/to/" + ecu_name + "/leader", 1, [this, i](const std_msgs::msg::Int8 msg) {this->onLeader(msg, i);});
      }

      subscription_shutdown_ = this->create_subscription<std_msgs::msg::Empty>(
          "/" + ecu_name + "/shutdown", 1, std::bind(&ECU::onShutdown, this, _1));
      subscription_link_crash_ = std::vector<rclcpp::Subscription<std_msgs::msg::Empty>::SharedPtr>(4);
      for (int i = 0; i < ecu_num; i++) {
        if (i == ecu_id) continue;
        subscription_link_crash_[i] = this->create_subscription<std_msgs::msg::Empty>(
          "/" + ecu_name + "/to/" + ecu_names[i] + "/link_crash", 1, [this, i](const std_msgs::msg::Empty msg) {this->onLinkCrash(msg, i);});
      }
      
      timer_ = create_wall_timer(100ms, std::bind(&ECU::onTimer, this));
    }

  private:
    void onTimer()
    {
      RCLCPP_INFO(this->get_logger(), "'%s' assumes leader is %d", ecu_name.c_str(), current_leader);

      // send heartbeats to other nodes
      for (int i = 0; i < ecu_num; i++) {
        if (i == ecu_id) continue;
        if (external_link_crash[i]) continue;

        auto message = std_msgs::msg::Int8();
        publisher_heartbeats_[i]->publish(message);
      }

      // detect timeout
      for (int i = 0; i < ecu_num; i++) {
        if (i == ecu_id) continue;

        if (is_connected[i]) {

          // if timeout is detected, increment election_id and start leader election
          if ((this->now() - received_time[i]).seconds() > timeout_threshold) {
            RCLCPP_INFO(this->get_logger(), "'%s' detected '%s' heartbeat timeout", ecu_name.c_str(), ecu_names[i].c_str());
            is_connected[i] = false;
            election_id = (election_id + 1) & (election_id_cycle - 1); // same as (election_id + 1) % election_id_cycle
            start_leader_election();
          }
        }
      }
    }

    void onShutdown([[maybe_unused]] const std_msgs::msg::Empty & msg) {
      rclcpp::shutdown();
    }

    void onLinkCrash([[maybe_unused]] const std_msgs::msg::Empty & msg, const int id) {
      external_link_crash[id] = true;
    }

    void onHeartbeat([[maybe_unused]] const std_msgs::msg::Int8 & msg, const int id)
    {
      is_connected[id] = true;
      received_time[id] = this->now();
    }

    void onElection(const std_msgs::msg::Int8 & msg, const int id)
    {
      if (external_link_crash[id]) return;

      // The low 4 bits in msg are used for connected_cound
      // The high 4 bits in msg are used for electon_id
      // ex: msg = 0b00110001 -> connected_cound=0001, election_id=0011
      int tmp_data = msg.data;
      int election_id_in_msg = (tmp_data >> 4);

      int connected_count = count_connected();
      int connected_count_in_msg = tmp_data & 0b1111;

      // The low 4 bits in msg are used for reply
      // The high 4 bits in msg are used for electon_id
      // ex: msg = 0b00110001 -> reply=0001, election_id=0011
      auto reply = std_msgs::msg::Int8();
      if (connected_count > connected_count_in_msg) {
        reply.data = 0;
      } else if (connected_count == connected_count_in_msg) {
        reply.data = id <= ecu_id;
      } else {
        reply.data = 1;
      }
      reply.data |= (election_id_in_msg << 4);
      publisher_replys_[id]->publish(reply);

      // if election_id in msg is newer than electio_id, start election
      if (is_new_election(election_id_in_msg, election_id)) {
        election_id = election_id_in_msg;
        start_leader_election();
      }
    }

    void onReply(const std_msgs::msg::Int8 & msg)
    {
      // The low 4 bits in msg are used for reply
      // The high 4 bits in msg are used for electon_id
      // ex: msg = 0b00110001 -> reply=0001, election_id=0011
      int tmp_data = msg.data;
      int election_id_in_msg = (tmp_data >> 4);
      bool reply = (tmp_data & 1);

      reply_counts[election_id_in_msg]++;
      if (reply == true) leader_votes[election_id_in_msg]++;

      // if all replys has arrived, end election
      if (reply_counts[election_id_in_msg] == count_connected()) {
        end_leader_election(election_id_in_msg);
      }
    }

    void onLeader(const std_msgs::msg::Int8 & msg, const int id)
    {
      // The low 4 bits in msg are not used
      // The high 4 bits in msg are used for electon_id
      // ex: msg = 0b00110000 -> election_id=0011
      int tmp_data = msg.data;
      int election_id_in_msg = (tmp_data >> 4);
      if (election_id == election_id_in_msg) {
        current_leader = id;
      }
    }

    void start_leader_election() {
      RCLCPP_INFO(this->get_logger(), "'%s' started leader election", ecu_name.c_str());

      reply_counts[election_id] = 0;
      leader_votes[election_id] = 0;

      for (int i = 0; i < ecu_num; i++) {
        if (i == ecu_id) continue;
        if (external_link_crash[i]) continue;

        // The low 4 bits in election msg are used for connected_count
        // The high 4 bits in election msg are used for electon_id
        // ex: msg = 0b00110000 -> connected_count=0001, election_id=0011
        auto election = std_msgs::msg::Int8();
        election.data = count_connected();
        election.data |= (election_id << 4);
        publisher_elections_[i]->publish(election);
      }
    }

    void end_leader_election(int election_id_in_msg) {
      if (leader_votes[election_id_in_msg] == count_connected()) {
        current_leader = ecu_id;

        for (int i = 0; i < ecu_num; i++) {
          if (i == ecu_id) continue;
          if (external_link_crash[i]) continue;

          // The low 4 bits in msg are not used
          // The high 4 bits in msg are used for electon_id
          // ex: msg = 0b00110000 -> election_id=0011
          auto leader = std_msgs::msg::Int8();
          leader.data |= (election_id_in_msg << 4);
          publisher_leaders_[i]->publish(leader);
        }
      }

      RCLCPP_INFO(this->get_logger(), "'%s' ended leader election", ecu_name.c_str());
    }

    int count_connected() {
      int connected_count = 0;
      for (auto connected : is_connected) {
        if (connected) connected_count++;
      }
      return connected_count;
    }

    bool is_new_election(int target_id, int current_id) {
      // see: https://github.com/tier4/system_software_team_design_doc/blob/mrm/mrm/algorithm/leader_election.en.md#election_id-comparison-logic
      int diff = (target_id - current_id + election_id_cycle) & (election_id_cycle - 1);
      return diff > 0 && diff <= (election_id_cycle / 2);
    }
    
    rclcpp::TimerBase::SharedPtr timer_;

    // Publishers for heartbeat
    std::vector<rclcpp::Publisher<std_msgs::msg::Int8>::SharedPtr> publisher_heartbeats_;
    std::vector<rclcpp::Publisher<std_msgs::msg::Int8>::SharedPtr> publisher_elections_;
    std::vector<rclcpp::Publisher<std_msgs::msg::Int8>::SharedPtr> publisher_replys_;
    std::vector<rclcpp::Publisher<std_msgs::msg::Int8>::SharedPtr> publisher_leaders_;

    // Subscriptions for heartbeat
    std::vector<rclcpp::Subscription<std_msgs::msg::Int8>::SharedPtr> subscription_heartbeats_;
    std::vector<rclcpp::Subscription<std_msgs::msg::Int8>::SharedPtr> subscription_elections_;
    std::vector<rclcpp::Subscription<std_msgs::msg::Int8>::SharedPtr> subscription_replys_;
    std::vector<rclcpp::Subscription<std_msgs::msg::Int8>::SharedPtr> subscription_leaders_;

    rclcpp::Subscription<std_msgs::msg::Empty>::SharedPtr subscription_shutdown_;
    std::vector<rclcpp::Subscription<std_msgs::msg::Empty>::SharedPtr> subscription_link_crash_;

    // variables
    int ecu_num;
    std::vector<rclcpp::Time> received_time;
    std::vector<bool> is_connected;
    std::vector<std::string> ecu_names;
    std::vector<int> reply_counts;
    std::vector<int> leader_votes;
    std::vector<bool> external_link_crash;
    int election_id = 0;
    int election_id_cycle;

    // parameters
    int ecu_id;
    int current_leader;
    std::string ecu_name;
    double timeout_threshold;
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);
  rclcpp::spin(std::make_shared<ECU>());
  rclcpp::shutdown();
  return 0;
}
