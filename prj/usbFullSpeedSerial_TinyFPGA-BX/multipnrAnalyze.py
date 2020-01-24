#!/usr/bin/env python3

import csv
import re

import numpy as np
import seaborn as sns
import matplotlib
matplotlib.use("Agg") # Don't require X11.
import matplotlib.pyplot as plt

def mergeExtracted(): # {{{
    results = {}

    # multipnr/3/nextpnr.log:Info: Max frequency for clock 'clk_48MHz_$glb_clk': 61.23 MHz (PASS at 48.00 MHz)
    with open("multipnr/nextpnr.log.extracted") as fd:
        r = r'^\w*/(\d+)/.*: ([0-9\.]+)'
        for line in fd:
            seed, mhz = re.match(r, line).groups()

            if seed not in results.keys():
                results[seed] = {}

            results[seed]["nextpnr.log"] = mhz

    # multipnr/1/nextpnr.rpt:Total path delay: 16.16 ns (61.87 MHz)
    with open("multipnr/nextpnr.rpt.extracted") as fd:
        r = r'^\w*/(\d+)/.*\(([0-9\.]+)'
        for line in fd:
            seed, mhz = re.match(r, line).groups()

            if seed not in results.keys():
                results[seed] = {}

            results[seed]["nextpnr.rpt"] = mhz

    # multipnr/1/arachne.rpt:Total path delay: 16.16 ns (61.87 MHz)
    with open("multipnr/arachne.rpt.extracted") as fd:
        r = r'^\w*/(\d+)/.*\(([0-9\.]+)'
        for line in fd:
            seed, mhz = re.match(r, line).groups()

            if seed not in results.keys():
                results[seed] = {}

            results[seed]["arachne.rpt"] = mhz


    with open("multipnr/results.csv", 'w', newline='') as csvfile:
        w = csv.writer(csvfile)

        rows = ((seed, mhzs["nextpnr.log"], mhzs["nextpnr.rpt"], mhzs["arachne.rpt"]) \
            for seed,(mhzs) in results.items())

        w.writerows(rows)
# }}} def mergeExtracted

def plotResults(fname="multipnr/results.csv"): # {{{
    table = np.transpose(np.loadtxt(fname, delimiter=','))
    rowNextpnrLog = table[1]
    rowNextpnrRpt = table[2]
    rowArachneRpt = table[3]

    nextpnrLog_style = {"color":'r', "marker":"x"}
    nextpnrRpt_style = {"color":'g', "marker":"."}
    arachneRpt_style = {"color":'b', "marker":"^"}

    rowNextpnrLog_lim = \
        np.min(rowNextpnrLog), np.max(rowNextpnrLog)
    rowNextpnrRpt_lim = \
        np.min(rowNextpnrRpt), np.max(rowNextpnrRpt)
    rowArachneRpt_lim = \
        np.min(rowArachneRpt), np.max(rowArachneRpt)

    markers = [".", "o", "x", "^", "s", "*", "", "", "", ""]

    # figsize used to set dimensions in inches.
    # ax.set_aspect() doesn't work for KDE where Y-axis is scaled.
    figsize = (16, 9)

    fignum = 0
    fig = plt.figure(fignum, figsize=figsize)

    sns.kdeplot(rowNextpnrLog, label="nextpnr.log", markevery=500, **nextpnrLog_style)
    sns.kdeplot(rowNextpnrRpt, label="nextpnr.rpt", markevery=500, **nextpnrRpt_style)
    sns.kdeplot(rowArachneRpt, label="arachne.rpt", markevery=500, **arachneRpt_style)

    plt.text(rowNextpnrLog_lim[0], 0.152, "%0.02f" % rowNextpnrLog_lim[0], fontsize=9)
    plt.text(rowNextpnrLog_lim[1], 0.152, "%0.02f" % rowNextpnrLog_lim[1], fontsize=9)
    plt.errorbar(rowNextpnrLog_lim, 0.15, **nextpnrLog_style)

    plt.text(rowNextpnrRpt_lim[0], 0.102, "%0.02f" % rowNextpnrRpt_lim[0], fontsize=9)
    plt.text(rowNextpnrRpt_lim[1], 0.102, "%0.02f" % rowNextpnrRpt_lim[1], fontsize=9)
    plt.errorbar(rowNextpnrRpt_lim, 0.10, **nextpnrRpt_style)

    plt.text(rowArachneRpt_lim[0], 0.052, "%0.02f" % rowArachneRpt_lim[0], fontsize=9)
    plt.text(rowArachneRpt_lim[1], 0.052, "%0.02f" % rowArachneRpt_lim[1], fontsize=9)
    plt.errorbar(rowArachneRpt_lim, 0.05, **arachneRpt_style)

    plt.legend()
    plt.yticks([])
    plt.xlabel("MHz")
    plt.xlim(35, 75)
    plt.ylim(0, 0.2)
    plt.savefig(fname + ".pdf", bbox_inches="tight")
    plt.savefig(fname + ".png", bbox_inches="tight")
    plt.close()
# }}} def plotResults

if __name__ == "__main__":
    mergeExtracted()
    plotResults()

