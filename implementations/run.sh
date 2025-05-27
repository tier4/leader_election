
ITERATION=1

for experiment_id in $(seq 0 $ITERATION); do

docker compose up -d

sleep 2

# CPU load
# docker exec main_ecu stress-ng --cpu 2 --cpu-load 50 &
# docker exec sub_ecu stress-ng --cpu 2 --cpu-load 50 &
# docker exec main_vcu stress-ng --cpu 2 --cpu-load 50 &
# docker exec sub_vcu stress-ng --cpu 2 --cpu-load 50 &

# copy leader_election executable
docker cp ./leader_election main_ecu:/leader_election
docker cp ./leader_election sub_ecu:/leader_election
docker cp ./leader_election main_vcu:/leader_election
docker cp ./leader_election sub_vcu:/leader_election

# run leader election
docker exec main_ecu /leader_election 0 $experiment_id &
docker exec sub_ecu /leader_election 1 $experiment_id &
docker exec main_vcu /leader_election 2 $experiment_id &
docker exec sub_vcu /leader_election 3 $experiment_id &

sleep 1

# stop main ecu
docker stop main_ecu

# echo disconnecting
# docker network disconnect docker_runner_me_mv main_ecu

sleep 1

# copy outputs
docker cp sub_ecu:/node1_exp$experiment_id.csv ./output/
docker cp main_vcu:/node2_exp$experiment_id.csv ./output/
docker cp sub_vcu:/node3_exp$experiment_id.csv ./output/

docker compose rm -sf

sleep 1

docker network prune --force

sleep 1

done
