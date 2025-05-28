import os
import matplotlib
matplotlib.use('TkAgg')

import matplotlib.pyplot as plt

ITERATION = 100

if __name__ == "__main__":

    latencies = []

    for i in range(1, ITERATION + 1):
        first_detection_timestamp = 100000000000
        final_election_timestamp = 0

        for j in range(0, 4): # link crash
        # for j in range(1, 4): # node crash
            with open(f'./output_node/node{j}_exp{i}.csv', 'r') as f:
                lines = f.readlines()

                for line in lines:
                    contents = line.split(',')
                    if contents[0] == '1':
                        detection_timestamp = float(contents[1])
                        if detection_timestamp < first_detection_timestamp:
                            first_detection_timestamp = detection_timestamp
                    elif contents[0] == '2':
                        election_timestamp = float(contents[1])
                        if election_timestamp > final_election_timestamp:
                            final_election_timestamp = election_timestamp
                    else:
                        print(f"Unknown event: {line} node{j} exp{i}")


        # calculate latency
        latency = final_election_timestamp - first_detection_timestamp
        latencies.append(latency * 1000)


    # plot latency
    plt.figure(figsize=(5, 5))

    # Box plot
    plt.subplot(1, 1, 1)
    plt.boxplot(latencies)
    plt.ylabel('Latency (ms)')
    plt.title('Latency Distribution')
    plt.grid(True)

    plt.tight_layout()
    plt.show()
