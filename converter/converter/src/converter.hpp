
#include <memory>

#include "rclcpp/rclcpp.hpp"

// Autoware
#include <autoware_adapi_v1_msgs/msg/mrm_state.hpp>

// socket
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>

using autoware_adapi_v1_msgs::msg::MrmState;

using namespace std::literals::chrono_literals;

struct peer_info
{
  int send_socket;
  int listen_socket;
  struct addrinfo *send_addrinfo;
  struct addrinfo *listen_addrinfo;
};


class Converter : public rclcpp::Node
{
  public:
    Converter();

  private:
    rclcpp::Subscription<MrmState>::SharedPtr sub_mrm_state_;
    rclcpp::Publisher<MrmState>::SharedPtr pub_mrm_state_;

    struct peer_info leader_elector;

    void on_mrm_state(const MrmState & msg) const;
    
    rclcpp::TimerBase::SharedPtr timer_;
    void onTimer();

    // socket
    void prepare_address_info(char *address, char *port, struct addrinfo **res);
    int get_socket(struct addrinfo *address_info);
};
