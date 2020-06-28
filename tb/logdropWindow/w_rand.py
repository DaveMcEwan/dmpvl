#!/usr/bin/env python3

# Simulate the output of putting a uniform random variable through the logdrop
# windowing function.
# Multiple ways of describing the same thing produce similar distributions.

import seaborn as sns
import matplotlib
matplotlib.use("Agg") # Don't require X11.
import matplotlib.pyplot as plt
import numpy as np
from math import *

n = 256 # WINLEN
figsize = (16,10)

# {{{ PMF
p256 = np.empty(256)
p256[0:2] = 9
p256[2:4] = 7
p256[4:8] = 6
p256[8:16] = 5
p256[16:32] = 4
p256[32:64] = 3
p256[64:128] = 2
p256[128:256] = 1
p256 /= 9

p128 = np.empty(256)
p128[0:4] = 8
p128[4:8] = 6
p128[8:16] = 5
p128[16:32] = 4
p128[32:64] = 3
p128[64:128] = 2
p128[128:256] = 1
p128 /= 8

p64 = np.empty(256)
p64[0:8] = 7
p64[8:16] = 5
p64[16:32] = 4
p64[32:64] = 3
p64[64:128] = 2
p64[128:256] = 1
p64 /= 7

p32 = np.empty(256)
p32[0:16] = 6
p32[16:32] = 4
p32[32:64] = 3
p32[64:128] = 2
p32[128:256] = 1
p32 /= 6

p16 = np.empty(256)
p16[0:32] = 5
p16[32:64] = 3
p16[64:128] = 2
p16[128:256] = 1
p16 /= 5

p8 = np.empty(256)
p8[0:64] = 4
p8[64:128] = 2
p8[128:256] = 1
p8 /= 4

ys = [
    (p8, 'g-', "n=8"),
    #(p16, '-', "n=16"),
    (p32, 'k-', "n=32"),
    #(p64, '-', "n=64"),
    #(p128, '-', "n=128"),
    (p256, 'b-', "n=256"),
]

def plotManual(ys, nm):
    fig = plt.figure(0, figsize=(8, 5))
    plt.rc("text", usetex=True)
    plt.rc("font", family="serif", size=12)
    plt.xticks([2**v-1 for v in range(3, 8+1)])
    for y,s,l in ys:
        plt.plot(y, s, label=l)
    plt.xlim(0, 255)
    plt.xlabel("Byte value as unsigned integer")
    plt.ylim(0, 1.05)
    plt.yticks([])
    plt.ylabel("Probability")
    plt.legend()
    plt.savefig(nm + ".pdf", bbox_inches="tight")
    plt.close()

plotManual(ys, "logdropWindow_PMF")

# }}} PMF


def plot(y, nm):
    fig = plt.figure(0, figsize=figsize)
    plt.xticks(list(range(0, 256, 8)))
    sns.distplot(y, bins=list(range(256)))
    plt.xlim(0, 255)
    plt.savefig(nm + ".png", bbox_inches="tight")
    plt.close()


### Proscribed distribution.
y1 = np.zeros(2560000)
y1[      0:1280000] = np.random.randint(0,256, 1280000)
y1[1280000:1920000] = np.random.randint(0,128, 640000)
y1[1920000:2240000] = np.random.randint(0,64, 320000)
y1[2240000:2400000] = np.random.randint(0,32, 160000)
y1[2400000:2480000] = np.random.randint(0,16, 80000)
y1[2480000:2520000] = np.random.randint(0,8, 40000)
y1[2520000:2540000] = np.random.randint(0,4, 20000)
y1[2540000:2560000] = np.random.randint(0,2, 20000)

plot(y1, "w_rand.np1")


nSamples = int(1e7)

### Derived distribution from uniform, nice equation.
y2 = np.zeros(nSamples)
ts_abs = range(nSamples)
for ta in ts_abs:
    t = ta % 256
    w = 2**( ceil(log(min(t+1, n-t), 2)) - log(n/2, 2) )
    x = np.random.randint(0, n)
    y2[ta] = int(w*x)

plot(y2, "w_rand.np2")


### Derived distribution from uniform, abstract model.
onehotIdxN = int(log2(n/2))
def w_1idx(t, n):
    assert 0 < t <= n, (t, n)

    if t <= n / 2:
        a = t
    else:
        a = n - t + 1

    shft = onehotIdxN - ceil(log(a, 2))

    return 1/2**shft

y3 = np.zeros(nSamples)
ts_abs = range(nSamples)
for ta in ts_abs:
    t = ta % n
    w = w_1idx(t+1, n)
    x = np.random.randint(0, n)
    y3[ta] = int(w*x)

plot(y3, "w_rand.np3")

