/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1556
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1607
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1611
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1673
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1676
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1695
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1696
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1699
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1701
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1703
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1705
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1706
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1711
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1712
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1713
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1721
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1722
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1725
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1727
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1728
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1733
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1735
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1737
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1738
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1743
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1744
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1745
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1753
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1754
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1756
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1761
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1770
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1771
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1772
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1773
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1775
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1777
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1778
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1783
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1784
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1792
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1793
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1807
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1808
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1809
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1810
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1813
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1814
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1817
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1829
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1830
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1833
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1834
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1835
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1836
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1837
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1838
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1841
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1843
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1847
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1848
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1856
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1857
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1865
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1866
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1870
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1872
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1876
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1877
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1878
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1879
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1880
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1881
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1882
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1883
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1884
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1887
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1890
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1893
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1896
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison2350 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1695.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1673.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1673.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1695.actual_graph_bounds.2
  linarith
#print axioms comparison2350
theorem comparison2351 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1696.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1676.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1676.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1696.actual_graph_bounds.2
  linarith
#print axioms comparison2351
theorem comparison2352 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1701.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1699.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1699.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1701.actual_graph_bounds.2
  linarith
#print axioms comparison2352
theorem comparison2353 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1705.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1703.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1703.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1705.actual_graph_bounds.2
  linarith
#print axioms comparison2353
theorem comparison2354 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1711.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1706.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1706.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1711.actual_graph_bounds.2
  linarith
#print axioms comparison2354
theorem comparison2355 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1721.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1712.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1712.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1721.actual_graph_bounds.2
  linarith
#print axioms comparison2355
theorem comparison2356 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1722.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1713.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1713.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1722.actual_graph_bounds.2
  linarith
#print axioms comparison2356
theorem comparison2357 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1727.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1725.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1725.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1727.actual_graph_bounds.2
  linarith
#print axioms comparison2357
theorem comparison2358 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1733.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1728.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1728.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1733.actual_graph_bounds.2
  linarith
#print axioms comparison2358
theorem comparison2359 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1737.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1735.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1735.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1737.actual_graph_bounds.2
  linarith
#print axioms comparison2359
theorem comparison2360 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1743.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1738.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1738.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1743.actual_graph_bounds.2
  linarith
#print axioms comparison2360
theorem comparison2361 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1753.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1744.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1744.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1753.actual_graph_bounds.2
  linarith
#print axioms comparison2361
theorem comparison2362 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1754.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1745.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1745.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1754.actual_graph_bounds.2
  linarith
#print axioms comparison2362
theorem comparison2363 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1770.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1771.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1771.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1770.actual_graph_bounds.2
  linarith
#print axioms comparison2363
theorem comparison2364 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1771.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1712.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1712.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1771.actual_graph_bounds.2
  linarith
#print axioms comparison2364
theorem comparison2365 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1772.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1744.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1744.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1772.actual_graph_bounds.2
  linarith
#print axioms comparison2365
theorem comparison2366 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1773.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1756.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1756.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1773.actual_graph_bounds.2
  linarith
#print axioms comparison2366
theorem comparison2367 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1777.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1775.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1775.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1777.actual_graph_bounds.2
  linarith
#print axioms comparison2367
theorem comparison2368 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1783.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1778.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1778.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1783.actual_graph_bounds.2
  linarith
#print axioms comparison2368
theorem comparison2369 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1792.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1756.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1756.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1792.actual_graph_bounds.2
  linarith
#print axioms comparison2369
theorem comparison2370 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1793.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1784.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1784.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1793.actual_graph_bounds.2
  linarith
#print axioms comparison2370
theorem comparison2371 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1807.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1808.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1808.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1807.actual_graph_bounds.2
  linarith
#print axioms comparison2371
theorem comparison2372 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1808.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1713.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1713.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1808.actual_graph_bounds.2
  linarith
#print axioms comparison2372
theorem comparison2373 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1809.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1745.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1745.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1809.actual_graph_bounds.2
  linarith
#print axioms comparison2373
theorem comparison2374 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1810.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1784.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1784.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1810.actual_graph_bounds.2
  linarith
#print axioms comparison2374
theorem comparison2375 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1813.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1814.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1814.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1813.actual_graph_bounds.2
  linarith
#print axioms comparison2375
theorem comparison2376 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1829.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1830.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1830.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1829.actual_graph_bounds.2
  linarith
#print axioms comparison2376
theorem comparison2377 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1833.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1835.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1835.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1833.actual_graph_bounds.2
  linarith
#print axioms comparison2377
theorem comparison2378 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1834.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1611.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1611.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1834.actual_graph_bounds.2
  linarith
#print axioms comparison2378
theorem comparison2379 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1835.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1706.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1706.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1835.actual_graph_bounds.2
  linarith
#print axioms comparison2379
theorem comparison2380 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1836.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1728.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1728.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1836.actual_graph_bounds.2
  linarith
#print axioms comparison2380
theorem comparison2381 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1837.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1738.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1738.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1837.actual_graph_bounds.2
  linarith
#print axioms comparison2381
theorem comparison2382 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1838.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1778.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1778.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1838.actual_graph_bounds.2
  linarith
#print axioms comparison2382
theorem comparison2383 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1841.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1843.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1843.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1841.actual_graph_bounds.2
  linarith
#print axioms comparison2383
theorem comparison2384 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1857.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1857.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1856.actual_graph_bounds.2
  linarith
#print axioms comparison2384
theorem comparison2385 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1865.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1866.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1866.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1865.actual_graph_bounds.2
  linarith
#print axioms comparison2385
theorem comparison2386 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1872.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1872.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1870.actual_graph_bounds.2
  linarith
#print axioms comparison2386
theorem comparison2387 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1876.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1880.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1880.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1876.actual_graph_bounds.2
  linarith
#print axioms comparison2387
theorem comparison2388 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1877.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1881.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1881.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1877.actual_graph_bounds.2
  linarith
#print axioms comparison2388
theorem comparison2389 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1878.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1556.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1556.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1878.actual_graph_bounds.2
  linarith
#print axioms comparison2389
theorem comparison2390 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1879.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1607.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1607.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1879.actual_graph_bounds.2
  linarith
#print axioms comparison2390
theorem comparison2391 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1880.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1699.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1699.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1880.actual_graph_bounds.2
  linarith
#print axioms comparison2391
theorem comparison2392 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1881.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1703.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1703.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1881.actual_graph_bounds.2
  linarith
#print axioms comparison2392
theorem comparison2393 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1882.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1725.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1725.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1882.actual_graph_bounds.2
  linarith
#print axioms comparison2393
theorem comparison2394 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1883.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1735.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1735.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1883.actual_graph_bounds.2
  linarith
#print axioms comparison2394
theorem comparison2395 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1884.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1775.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1775.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1884.actual_graph_bounds.2
  linarith
#print axioms comparison2395
theorem comparison2396 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1887.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1847.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1847.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1887.actual_graph_bounds.2
  linarith
#print axioms comparison2396
theorem comparison2397 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1890.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1848.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1848.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1890.actual_graph_bounds.2
  linarith
#print axioms comparison2397
theorem comparison2398 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1893.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1817.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1817.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1893.actual_graph_bounds.2
  linarith
#print axioms comparison2398
theorem comparison2399 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1896.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1761.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1761.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1896.actual_graph_bounds.2
  linarith
#print axioms comparison2399
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
