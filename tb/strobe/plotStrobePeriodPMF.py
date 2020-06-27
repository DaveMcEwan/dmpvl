#!/usr/bin/env python3

from functools import lru_cache
from math import exp, pi, sqrt
import matplotlib.pyplot as plt

s = 100 # i_ctrlPeriodM1 + 1
js = (0.3, 0.5, 0.9) # i_ctrlJitter / 2**CTRL_JITTER_W

plotMinCount = 0
plotMaxCount = int(s * 1.5)
plotRangeCMF = range(plotMinCount, plotMaxCount+1)
plotRangePMF = range(len(plotRangeCMF)-1)


@lru_cache(maxsize=512)
def nodePr(count, nSteps, pathPr=(0.25, 0.5, 0.25)): # {{{
    '''Calculate probability of reaching count after n steps in trinomial dist.
       Intended to calculate distribution of period lengths in strobe.v for
       different values of i_ctrlJitter.
    '''

    assert isinstance(count, int), (type(count), count)
    assert 0 <= count <= (nSteps*2), count

    assert isinstance(nSteps, int), (type(nSteps), nSteps)
    assert 0 < nSteps, nSteps

    assert isinstance(pathPr, (tuple, list)), (type(pathPr), pathPr)
    assert 3 == len(pathPr), pathPr
    assert all(isinstance(p, float) for p in pathPr), pathPr
    assert all(p <= 1.0 for p in pathPr), pathPr
    assert (1.0-0.001) < sum(pathPr) < (1.0+0.001), (sum(pathPr), pathPr)

    if 1 == nSteps:
        ret = pathPr[count]
    elif 0 == count:
        ret = nodePr(count,   nSteps-1, pathPr=pathPr) * pathPr[0]
    elif 1 == count:
        ret = nodePr(count-1, nSteps-1, pathPr=pathPr) * pathPr[1] + \
              nodePr(count,   nSteps-1, pathPr=pathPr) * pathPr[0]
    elif (nSteps*2) == count:
        ret = nodePr(count-2, nSteps-1, pathPr=pathPr) * pathPr[2]
    elif (nSteps*2 - 1) == count:
        ret = nodePr(count-2, nSteps-1, pathPr=pathPr) * pathPr[2] + \
              nodePr(count-1, nSteps-1, pathPr=pathPr) * pathPr[1]
    else:
        ret = nodePr(count-2, nSteps-1, pathPr=pathPr) * pathPr[2] + \
              nodePr(count-1, nSteps-1, pathPr=pathPr) * pathPr[1] + \
              nodePr(count,   nSteps-1, pathPr=pathPr) * pathPr[0]

    return ret
# }}} def nodePr

def atLeastPr(count, nSteps, j): # {{{
    '''Probability of reaching at least count over n steps.
       Set count to the desired period, then the CMF of period finishing in n
       steps is calculated with atLeastPr( periodLength, n ∊ [0, ∞) )
    '''
    if count > (nSteps*2):
        ret = 0.0
    else:
        pathPr = (j/2, 1-j, j/2)
        ret = sum(nodePr(d, nSteps, pathPr=pathPr) \
                  for d in range(count, nSteps*2+1))

    return ret
# }}} def atLeastPr

def gaussianPDF(x, mu=0, sigma=1): # {{{
    '''Gaussian function
    mu is the peak of the curve.
    sigma is spread of the curve.
    '''
    x = float(x)
    mu = float(mu)
    sigma = float(sigma)

    r = (1 / (sigma * sqrt(2 * pi))) * exp(-0.5 * ((x - mu) / sigma)**2)
    return r
# }}} def gaussianPDF

def plot(s, js, CMFs, PMFs): # {{{
    assert len(js) == len(PMFs)
    assert len(CMFs) == len(PMFs)
    assert len(CMFs[0]) == len(PMFs[0])
    assert all(len(c) == len(CMFs[0]) for c in CMFs)
    assert all(len(p) == len(PMFs[0]) for p in PMFs)

    pltRange = range(len(CMFs[0]))

    plt.figure(figsize=(8, 5))
    #plt.title("PMF of #cycles in sample period")
    #plt.title("j = i_ctrlJitter/2**CTRL_JITTER_W; i_ctrlPeriodM1 = %d" % (s-1))

    for j, pmf in zip(js, PMFs):
        plt.plot(pmf, label="j=%0.1f" % j)

    plt.legend()
    plt.xlim(plotMinCount, plotMaxCount)

    plt.savefig("strobePeriodPMF.pdf", bbox_inches='tight')
    plt.close()

    # Gaussian approximation
    mu = s
    plt.figure(figsize=(8, 5))
    for j in js:
        sigma = sqrt(s * j)
        N = [gaussianPDF(x, mu, sigma) for x in pltRange]
        plt.plot(N, label="variance=%d*%0.01f" % (s, j))
    plt.legend()
    plt.xlim(plotMinCount, plotMaxCount)
    plt.savefig("strobePeriodApproxPDF.pdf", bbox_inches='tight')
    plt.close()

# }}} def plot

CMFs = []
PMFs = []
for j in js:
    cmf = []
    for n in plotRangeCMF:
        #print("atLeastPr(count=%d, nSteps=%d, j=%f)" % (s, n, j))
        cmf.append(atLeastPr(s, n, j))
    #print("CMF", j, cmf)
    CMFs.append(cmf)

    pmf = [0]
    for i in plotRangePMF:
        pmf.append(cmf[i+1] - cmf[i])
    #print("PMF", j, pmf)
    PMFs.append(pmf)

plot(s, js, CMFs, PMFs)
