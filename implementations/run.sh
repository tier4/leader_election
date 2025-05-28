ITERATION=3

make clean
make all

docker network prune --force

for experiment_id in $(seq 1 $ITERATION); do

echo "--------------------------------"
echo "Experiment $experiment_id"
echo "--------------------------------"

docker compose up -d

sleep 1

# CPU load
# docker exec main_ecu stress-ng --cpu 2 --cpu-load 50 &
# docker exec sub_ecu stress-ng --cpu 2 --cpu-load 50 &
# docker exec main_vcu stress-ng --cpu 2 --cpu-load 50 &
# docker exec sub_vcu stress-ng --cpu 2 --cpu-load 50 &

# run leader election
docker exec main_ecu /leader_election/leader_election 0 $experiment_id &
docker exec sub_ecu /leader_election/leader_election 1 $experiment_id &
docker exec main_vcu /leader_election/leader_election 2 $experiment_id &
docker exec sub_vcu /leader_election/leader_election 3 $experiment_id &

sleep 1

# main ecu node crash
docker exec main_ecu pkill -SIGINT leader_election

# main_ecu - sub_ecu link crash
# docker network disconnect docker_runner_me_se main_ecu

sleep 1

# docker exec sub_ecu pkill leader_election
# docker exec main_vcu pkill leader_election
# docker exec sub_vcu pkill leader_election

docker compose rm -sf

sleep 1

done
