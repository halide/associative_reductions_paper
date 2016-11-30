SOCKET=$1
env HL_NUM_THREADS=$(cat /proc/cpuinfo | grep "physical id.* $SOCKET" | wc -l) numactl --cpunodebind=$1 bash --rcfile <(cat ~/.bashrc; echo 'export PS1="${PS1}'"${SOCKET}> "'"') -i
