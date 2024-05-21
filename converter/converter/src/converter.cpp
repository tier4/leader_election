
#include "converter.hpp"

int id;

Converter::Converter() : Node("converter")
{
  // prepare subscribers
  using std::placeholders::_1;
  sub_mrm_state_ = this->create_subscription<MrmState>(
    "/system/fail_safe/mrm_state", 10, std::bind(&Converter::on_mrm_state, this, _1));
  timer_ =
    rclcpp::create_timer(this, get_clock(), 10ms, std::bind(&Converter::onTimer, this));
  pub_mrm_state_ = create_publisher<MrmState>("/system/fail_safe/mrm_state", rclcpp::QoS{1});

  // prepare socket

  if (id == 0) {
    // Main ECU
    // Currently, recv mrm_state topic and send UDP only
    char addr[16] = "127.0.0.1";
    char send_port[16] = "8000";
    prepare_address_info(addr, send_port, &leader_elector.send_addrinfo);
    leader_elector.send_socket = get_socket(leader_elector.send_addrinfo);
  } else if (id == 1) {
    // Sub ECU
    // Currently, recv UDP and send mrm_state topic only
    char addr[16] = "127.0.0.1";
    char listen_port[16] = "8001";
    prepare_address_info(addr, listen_port, &leader_elector.listen_addrinfo);
    leader_elector.listen_socket = get_socket(leader_elector.listen_addrinfo);

    struct timeval recv_to;
    recv_to.tv_sec = 0;
    recv_to.tv_usec = 1;
    setsockopt(leader_elector.listen_socket, SOL_SOCKET, SO_RCVTIMEO, &recv_to, sizeof(recv_to));
    struct addrinfo *address_info = leader_elector.listen_addrinfo;
    if (bind(leader_elector.listen_socket, address_info->ai_addr, address_info->ai_addrlen) == -1) {
        fprintf(stderr, "Error with binding receiver to port\n");
        exit(1);
    }
  }
}

void Converter::on_mrm_state(const MrmState & msg) const
{
  if (msg.state == MrmState::MRM_OPERATING && msg.behavior == MrmState::EMERGENCY_STOP)
  {
    fprintf(stderr, "recv emerevency from Autoware\n");
    fprintf(stderr, "send emergency to leader_elector\n");

    uint64_t msg = 0;
    if (sendto(leader_elector.send_socket, &msg, sizeof(uint64_t), 0, leader_elector.send_addrinfo->ai_addr, leader_elector.send_addrinfo->ai_addrlen) == -1) {
        fprintf(stderr, "Error with sending data\n");
        exit(1);
    }
  }
}

void Converter::onTimer()
{
  struct sockaddr_storage from;
  socklen_t fromlen = sizeof(from);
  memset(&from, 0, sizeof(from));
  uint8_t recv_buf_size = 64;
  uint64_t recv_buf;
  if (recvfrom(leader_elector.listen_socket, &recv_buf, recv_buf_size, 0, (struct sockaddr *)&from, &fromlen) > 0) {
    fprintf(stderr, "recv emergency from leader_elector\n");
    fprintf(stderr, "send emergency to Autoware\n");

    MrmState msg;
    msg.stamp = this->now();
    msg.state = MrmState::MRM_OPERATING;
    msg.behavior == MrmState::EMERGENCY_STOP;
    pub_mrm_state_->publish(msg);
  }
}

void Converter::prepare_address_info(char *address, char *port, struct addrinfo **res)
{
  struct addrinfo hints;
  memset(&hints, 0, sizeof(hints));
  hints.ai_family = AF_INET;
  hints.ai_socktype = SOCK_DGRAM;

  int status = getaddrinfo(address, port, &hints, res);
  if (status != 0) {
    fprintf(stderr, "Error with getting address info, status = %s\n", gai_strerror(status));
    exit(1);
  }
}

int Converter::get_socket(struct addrinfo *address_info)
{
    int sock = socket(address_info->ai_family, address_info->ai_socktype, address_info->ai_protocol);
    if (sock == -1) {
        fprintf(stderr, "Error creating socket\n");
        exit(1);
    }

    return sock;
}

int main(int argc, char * argv[])
{
  id = strtol(argv[1], NULL, 10);

  rclcpp::init(argc, argv);
  rclcpp::spin(std::make_shared<Converter>());
  rclcpp::shutdown();
  return 0;
}