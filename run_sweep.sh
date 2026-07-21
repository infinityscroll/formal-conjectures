#!/bin/zsh
# Sweep all connected graphs on n=4..10 (Run A), then n=11 (Run B), 12-way parallel.
set -e
cd ~/wowii-campaign
GENG=/opt/homebrew/bin/geng
mkdir -p results

echo "=== Run A: n=4..9 (serial) ==="
for n in 4 5 6 7 8 9; do
  $GENG -cq $n | ./wowsweep $n > results/hits_n$n.txt 2> results/stats_n$n.txt
  echo "n=$n done: $(cat results/stats_n$n.txt)"
done

echo "=== Run A: n=10 (12-way) ==="
for k in {0..11}; do
  ( $GENG -cq 10 $k/12 | ./wowsweep 10 > results/hits_n10_$k.txt 2> results/stats_n10_$k.txt ) &
done
wait
cat results/hits_n10_*.txt > results/hits_n10.txt
echo "n=10 done: $(cat results/stats_n10_*.txt | awk -F'[= ]' '{t+=$3; nt+=$5} END {print "total="t" nontraceable="nt}')"

echo "=== Run B: n=11 (12-way) ==="
for k in {0..11}; do
  ( $GENG -cq 11 $k/12 | ./wowsweep 11 > results/hits_n11_$k.txt 2> results/stats_n11_$k.txt ) &
done
wait
cat results/hits_n11_*.txt > results/hits_n11.txt
echo "n=11 done: $(cat results/stats_n11_*.txt | awk -F'[= ]' '{t+=$3; nt+=$5} END {print "total="t" nontraceable="nt}')"
echo "ALL SWEEPS COMPLETE"
