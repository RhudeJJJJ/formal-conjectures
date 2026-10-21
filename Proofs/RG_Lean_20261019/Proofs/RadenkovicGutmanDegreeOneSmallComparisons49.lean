/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1517
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1518
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1522
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1523
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1532
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1533
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1537
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1554
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1555
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1559
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1560
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1569
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1601
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1605
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1606
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1617
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1621
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1638
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1697
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1698
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1702
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1723
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1724
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1734
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1774
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1885
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1888
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1898
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1932
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1981
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1982
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1983
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1984
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1985
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1986
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1987
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1988
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1989
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1991
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1993
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1994
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1995
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1996
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1997
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1998
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1999
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2000
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2001
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2002
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2003
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2004
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2005
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2006
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2007
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2008
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2009
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2010
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2011
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2012
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2013
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2014
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2015
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2016
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2017
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2018
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum2019
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison2450 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1981.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1698.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1698.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1981.actual_graph_bounds.2
  linarith
#print axioms comparison2450
theorem comparison2451 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1982.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1702.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1702.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1982.actual_graph_bounds.2
  linarith
#print axioms comparison2451
theorem comparison2452 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1983.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1723.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1723.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1983.actual_graph_bounds.2
  linarith
#print axioms comparison2452
theorem comparison2453 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1984.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1724.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1724.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1984.actual_graph_bounds.2
  linarith
#print axioms comparison2453
theorem comparison2454 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1985.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1734.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1734.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1985.actual_graph_bounds.2
  linarith
#print axioms comparison2454
theorem comparison2455 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1986.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1774.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1774.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1986.actual_graph_bounds.2
  linarith
#print axioms comparison2455
theorem comparison2456 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1517.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1989.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1989.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1517.actual_graph_bounds.2
  linarith
#print axioms comparison2456
theorem comparison2457 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1518.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1991.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1991.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1518.actual_graph_bounds.2
  linarith
#print axioms comparison2457
theorem comparison2458 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1522.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1993.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1993.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1522.actual_graph_bounds.2
  linarith
#print axioms comparison2458
theorem comparison2459 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1523.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1994.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1994.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1523.actual_graph_bounds.2
  linarith
#print axioms comparison2459
theorem comparison2460 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1532.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1995.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1995.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1532.actual_graph_bounds.2
  linarith
#print axioms comparison2460
theorem comparison2461 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1533.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1996.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1996.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1533.actual_graph_bounds.2
  linarith
#print axioms comparison2461
theorem comparison2462 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1537.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1997.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1997.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1537.actual_graph_bounds.2
  linarith
#print axioms comparison2462
theorem comparison2463 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1554.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1998.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1998.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1554.actual_graph_bounds.2
  linarith
#print axioms comparison2463
theorem comparison2464 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1555.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1999.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1999.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1555.actual_graph_bounds.2
  linarith
#print axioms comparison2464
theorem comparison2465 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1559.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2000.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2000.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1559.actual_graph_bounds.2
  linarith
#print axioms comparison2465
theorem comparison2466 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1560.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2001.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2001.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1560.actual_graph_bounds.2
  linarith
#print axioms comparison2466
theorem comparison2467 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1569.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2002.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2002.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1569.actual_graph_bounds.2
  linarith
#print axioms comparison2467
theorem comparison2468 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1601.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2003.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2003.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1601.actual_graph_bounds.2
  linarith
#print axioms comparison2468
theorem comparison2469 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1605.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2004.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2004.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1605.actual_graph_bounds.2
  linarith
#print axioms comparison2469
theorem comparison2470 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1606.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2005.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2005.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1606.actual_graph_bounds.2
  linarith
#print axioms comparison2470
theorem comparison2471 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1617.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2006.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2006.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1617.actual_graph_bounds.2
  linarith
#print axioms comparison2471
theorem comparison2472 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1621.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2007.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2007.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1621.actual_graph_bounds.2
  linarith
#print axioms comparison2472
theorem comparison2473 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1638.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2008.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2008.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1638.actual_graph_bounds.2
  linarith
#print axioms comparison2473
theorem comparison2474 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1697.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2009.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2009.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1697.actual_graph_bounds.2
  linarith
#print axioms comparison2474
theorem comparison2475 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1698.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2010.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2010.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1698.actual_graph_bounds.2
  linarith
#print axioms comparison2475
theorem comparison2476 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1702.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2011.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2011.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1702.actual_graph_bounds.2
  linarith
#print axioms comparison2476
theorem comparison2477 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1723.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2012.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2012.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1723.actual_graph_bounds.2
  linarith
#print axioms comparison2477
theorem comparison2478 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1724.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2013.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2013.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1724.actual_graph_bounds.2
  linarith
#print axioms comparison2478
theorem comparison2479 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1734.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2014.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2014.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1734.actual_graph_bounds.2
  linarith
#print axioms comparison2479
theorem comparison2480 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1774.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2015.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2015.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1774.actual_graph_bounds.2
  linarith
#print axioms comparison2480
theorem comparison2481 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1885.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2016.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2016.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1885.actual_graph_bounds.2
  linarith
#print axioms comparison2481
theorem comparison2482 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1888.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2017.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2017.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1888.actual_graph_bounds.2
  linarith
#print axioms comparison2482
theorem comparison2483 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1898.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2018.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2018.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1898.actual_graph_bounds.2
  linarith
#print axioms comparison2483
theorem comparison2484 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1932.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum2019.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum2019.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1932.actual_graph_bounds.2
  linarith
#print axioms comparison2484
theorem comparison2485 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1988.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1987.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1987.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1988.actual_graph_bounds.2
  linarith
#print axioms comparison2485
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
