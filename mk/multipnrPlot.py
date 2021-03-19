#!/usr/bin/env python3

import argparse
import csv
import re
import sys

import numpy as np
import seaborn as sns
import matplotlib
matplotlib.use("Agg") # Don't require X11.
import matplotlib.pyplot as plt

from dmppl.base import run

__version__ = "0.1.0"

def mergeExtracted(doArachne=False): # {{{
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

    if doArachne:
        # multipnr/1/arachne.rpt:Total path delay: 16.16 ns (61.87 MHz)
        with open("multipnr/arachne.rpt.extracted") as fd:
            r = r'^\w*/(\d+)/.*\(([0-9\.]+)'
            for line in fd:
                seed, mhz = re.match(r, line).groups()

                if seed not in results.keys():
                    results[seed] = {}

                results[seed]["arachne.rpt"] = mhz


    with open("multipnr/results.csv", 'w', newline='') as csvfile:

        def cols(table, doArachne=False):
            keys = ["nextpnr.log", "nextpnr.rpt"]
            if doArachne:
                keys.append("arachne.rpt")
            return [table[k] for k in keys]

        w = csv.writer(csvfile)

        rows = ((seed, *cols(mhzs, doArachne)) \
            for seed,(mhzs) in results.items())

        w.writerows(rows)
# }}} def mergeExtracted

def plotResults(fname="multipnr/results.csv", doArachne=False,
                xLo=35.0, xHi=75.0, yLo=0.0, yHi=0.25): # {{{

    # figsize used to set dimensions in inches.
    # ax.set_aspect() doesn't work for KDE where Y-axis is scaled.
    figsize = (16, 9)

    fignum = 0
    fig = plt.figure(fignum, figsize=figsize)
    table = np.transpose(np.loadtxt(fname, delimiter=','))

    # Ignore results of 0.0MHz
    rowNextpnrLog = np.ma.masked_equal(table[1], 0.0)
    rowNextpnrRpt = np.ma.masked_equal(table[2], 0.0)

    rowNextpnrLog_lim = \
        np.min(rowNextpnrLog), np.max(rowNextpnrLog)
    rowNextpnrRpt_lim = \
        np.min(rowNextpnrRpt), np.max(rowNextpnrRpt)

    nextpnrLog_style = {"color":'r', "marker":"x"}
    nextpnrRpt_style = {"color":'g', "marker":"."}

    sns.kdeplot(rowNextpnrLog, label="nextpnr.log", markevery=500, **nextpnrLog_style)
    sns.kdeplot(rowNextpnrRpt, label="nextpnr.rpt", markevery=500, **nextpnrRpt_style)

    plt.text(rowNextpnrLog_lim[0], 0.152, "%0.02f" % rowNextpnrLog_lim[0], fontsize=9)
    plt.text(rowNextpnrLog_lim[1], 0.152, "%0.02f" % rowNextpnrLog_lim[1], fontsize=9)
    plt.errorbar(rowNextpnrLog_lim, 0.15, **nextpnrLog_style)

    plt.text(rowNextpnrRpt_lim[0], 0.102, "%0.02f" % rowNextpnrRpt_lim[0], fontsize=9)
    plt.text(rowNextpnrRpt_lim[1], 0.102, "%0.02f" % rowNextpnrRpt_lim[1], fontsize=9)
    plt.errorbar(rowNextpnrRpt_lim, 0.10, **nextpnrRpt_style)

    if doArachne:
        rowArachneRpt = np.ma.masked_equal(table[3], 0.0)
        rowArachneRpt_lim = \
            np.min(rowArachneRpt), np.max(rowArachneRpt)
        arachneRpt_style = {"color":'b', "marker":"^"}
        sns.kdeplot(rowArachneRpt, label="arachne.rpt", markevery=500, **arachneRpt_style)

        plt.text(rowArachneRpt_lim[0], 0.052, "%0.02f" % rowArachneRpt_lim[0], fontsize=9)
        plt.text(rowArachneRpt_lim[1], 0.052, "%0.02f" % rowArachneRpt_lim[1], fontsize=9)
        plt.errorbar(rowArachneRpt_lim, 0.05, **arachneRpt_style)

    plt.legend()
    plt.yticks([])
    plt.xlabel("MHz")
    plt.xlim(xLo, xHi)
    plt.ylim(yLo, yHi)
    plt.savefig(fname + ".pdf", bbox_inches="tight")
    plt.savefig(fname + ".png", bbox_inches="tight")
    plt.close()
# }}} def plotResults

# {{{ argparser

argparser = argparse.ArgumentParser(
    description = "multipnrPlot - Merge and plot multiple PnR results.",
    formatter_class = argparse.ArgumentDefaultsHelpFormatter
)

argparser.add_argument("--doArachne",
    type=int, # Converted to bool later.
    default=0,
    help="Include legacy tool arachne-pnr.")

argparser.add_argument("--xlim",
    type=str,
    default="35,75",
    help="Limits for X-axis (MHz) like '35,75'.")

argparser.add_argument("--ylim",
    type=str,
    default="0,0.25",
    help="Limits for Y-axis like '0,0.25'.")

# }}} argparser

def main(args) -> int: # {{{
    '''
    '''
    doArachne = bool(args.doArachne)
    xLo, xHi = [float(x) for x in args.xlim.split(',')]
    yLo, yHi = [float(y) for y in args.ylim.split(',')]

    mergeExtracted(doArachne=doArachne)
    plotResults(doArachne=doArachne,
                xLo=xLo, xHi=xHi, yLo=yLo, yHi=yHi)

    return 0
# }}} def main

def entryPoint(argv=sys.argv):
    return run(__name__, argv=argv)

if __name__ == "__main__":
    sys.exit(entryPoint())

