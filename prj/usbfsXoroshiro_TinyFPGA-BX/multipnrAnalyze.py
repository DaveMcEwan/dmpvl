#!/usr/bin/env python3

import csv
import re

import numpy as np
import seaborn as sns
import matplotlib
matplotlib.use("Agg") # Don't require X11.
import matplotlib.pyplot as plt

def mergeExtracted(path="multipnr"): # {{{
    results = {}

    # multipnr/3/nextpnr.log:Info: Max frequency for clock 'clk_48MHz_$glb_clk': 61.23 MHz (PASS at 48.00 MHz)
    with open("%s/nextpnr.log.extracted" % path) as fd:
        r = r'^\w*/(\d+)/.*: ([0-9\.]+)'
        for line in fd:
            seed, mhz = re.match(r, line).groups()

            if seed not in results.keys():
                results[seed] = {}

            results[seed]["nextpnr.log"] = mhz

    # multipnr/1/nextpnr.rpt:Total path delay: 16.16 ns (61.87 MHz)
    with open("%s/nextpnr.rpt.extracted" % path) as fd:
        r = r'^\w*/(\d+)/.*\(([0-9\.]+)'
        for line in fd:
            seed, mhz = re.match(r, line).groups()

            if seed not in results.keys():
                results[seed] = {}

            results[seed]["nextpnr.rpt"] = mhz


    with open("%s/results.csv" % path, 'w', newline='') as csvfile:
        w = csv.writer(csvfile)

        rows = ((seed, mhzs["nextpnr.log"], mhzs["nextpnr.rpt"]) \
            for seed,(mhzs) in results.items())

        w.writerows(rows)
# }}} def mergeExtracted

def plotResults(paths=["multipnr"], names=["generic"]): # {{{
    assert len(paths) == len(names), (paths, names)

    # figsize used to set dimensions in inches.
    # ax.set_aspect() doesn't work for KDE where Y-axis is scaled.
    figsize = (16, 9)

    fignum = 0
    fig = plt.figure(fignum, figsize=figsize)

    markers = ['.', 'o', 'x', '^', 's', '*', '', '', '', '']
    colors = ['k', 'g', 'b', 'r', 'y', 'm', '', '', '', '']

    for i,(path,name) in enumerate(zip(paths, names)):
        fname = "%s/results.csv" % path
        table = np.transpose(np.loadtxt(fname, delimiter=','))

        rowNextpnrLog = table[1]
        #rowNextpnrRpt = table[2]

        rowNextpnrLog_lim = \
            np.min(rowNextpnrLog), np.max(rowNextpnrLog)

        style = {"color": colors[i], "marker": markers[i]}

        sns.kdeplot(rowNextpnrLog, label=name, markevery=500, **style)
        #sns.distplot(rowNextpnrLog, label=name, color=colors[i], bins=np.arange(50, 72, 1.0))
        barVerticalPosition = 0.5 - i*0.05
        plt.text(rowNextpnrLog_lim[0], barVerticalPosition + 0.002,
                 "%0.02f" % rowNextpnrLog_lim[0], fontsize=9)
        plt.text(rowNextpnrLog_lim[1], barVerticalPosition + 0.002,
                 "%0.02f" % rowNextpnrLog_lim[1], fontsize=9)
        plt.errorbar(rowNextpnrLog_lim, barVerticalPosition, **style)

        #rowNextpnrRpt_lim = \
        #    np.min(rowNextpnrRpt), np.max(rowNextpnrRpt)
        #nextpnrRpt_style = {"color":'g', "marker":"."}
        #sns.kdeplot(rowNextpnrRpt, label="nextpnr.rpt", markevery=500, **nextpnrRpt_style)
        #plt.text(rowNextpnrRpt_lim[0], 0.102, "%0.02f" % rowNextpnrRpt_lim[0], fontsize=9)
        #plt.text(rowNextpnrRpt_lim[1], 0.102, "%0.02f" % rowNextpnrRpt_lim[1], fontsize=9)
        #plt.errorbar(rowNextpnrRpt_lim, 0.10, **nextpnrRpt_style)

    plt.legend()
    plt.yticks([])
    plt.xlabel("MHz")
    plt.xlim(41, 71)
    #plt.ylim(0, 0.6)
    plt.savefig("multipnr.pdf", bbox_inches="tight")
    plt.savefig("multipnr.png", bbox_inches="tight")
    plt.savefig("multipnr.svg", bbox_inches="tight")
    plt.close()
# }}} def plotResults

algos = {
    0: "baseline (no PRNG)",
    1: "xoroshiro128+",
    2: "xoshiro128++",
    3: "xoshiro128+",
    4: "xoshiro256+",
    5: "xoroshiro64*",
}
if __name__ == "__main__":
    paths = ["multipnr.ALGORITHM=%d" % i for i,nm in algos.items()]
    names = [nm for i,nm in algos.items()]
    for path in paths:
        mergeExtracted(path)
    plotResults(paths, names)

