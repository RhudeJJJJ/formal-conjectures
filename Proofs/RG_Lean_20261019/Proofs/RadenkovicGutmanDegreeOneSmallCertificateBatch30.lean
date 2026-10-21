/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1500
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1501
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1502
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1503
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1504
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1505
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1506
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1507
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1508
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1509
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1510
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1511
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1512
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1513
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1514
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1515
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1516
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1517
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1518
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1519
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1520
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1521
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1522
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1523
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1524
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1525
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1526
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1527
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1528
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1529
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1530
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1531
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1532
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1533
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1534
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1535
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1536
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1537
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1538
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1539
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1540
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1541
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1542
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1543
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1544
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1545
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1546
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1547
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1548
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1549
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys30 : ∀ k ∈ keys30, Certified k := by
  apply certified_cons (by exact certified1500)
  apply certified_cons (by exact certified1500swap)
  apply certified_cons (by exact certified1501)
  apply certified_cons (by exact certified1502)
  apply certified_cons (by exact certified1502swap)
  apply certified_cons (by exact certified1503)
  apply certified_cons (by exact certified1504)
  apply certified_cons (by exact certified1504swap)
  apply certified_cons (by exact certified1505)
  apply certified_cons (by exact certified1506)
  apply certified_cons (by exact certified1506swap)
  apply certified_cons (by exact certified1507)
  apply certified_cons (by exact certified1508)
  apply certified_cons (by exact certified1508swap)
  apply certified_cons (by exact certified1509)
  apply certified_cons (by exact certified1510)
  apply certified_cons (by exact certified1510swap)
  apply certified_cons (by exact certified1511)
  apply certified_cons (by exact certified1512)
  apply certified_cons (by exact certified1512swap)
  apply certified_cons (by exact certified1513)
  apply certified_cons (by exact certified1514)
  apply certified_cons (by exact certified1514swap)
  apply certified_cons (by exact certified1515)
  apply certified_cons (by exact certified1516)
  apply certified_cons (by exact certified1516swap)
  apply certified_cons (by exact certified1517)
  apply certified_cons (by exact certified1518)
  apply certified_cons (by exact certified1518swap)
  apply certified_cons (by exact certified1519)
  apply certified_cons (by exact certified1520)
  apply certified_cons (by exact certified1520swap)
  apply certified_cons (by exact certified1521)
  apply certified_cons (by exact certified1522)
  apply certified_cons (by exact certified1522swap)
  apply certified_cons (by exact certified1523)
  apply certified_cons (by exact certified1524)
  apply certified_cons (by exact certified1524swap)
  apply certified_cons (by exact certified1525)
  apply certified_cons (by exact certified1526)
  apply certified_cons (by exact certified1526swap)
  apply certified_cons (by exact certified1527)
  apply certified_cons (by exact certified1528)
  apply certified_cons (by exact certified1528swap)
  apply certified_cons (by exact certified1529)
  apply certified_cons (by exact certified1530)
  apply certified_cons (by exact certified1530swap)
  apply certified_cons (by exact certified1531)
  apply certified_cons (by exact certified1532)
  apply certified_cons (by exact certified1532swap)
  apply certified_cons (by exact certified1533)
  apply certified_cons (by exact certified1534)
  apply certified_cons (by exact certified1534swap)
  apply certified_cons (by exact certified1535)
  apply certified_cons (by exact certified1536)
  apply certified_cons (by exact certified1536swap)
  apply certified_cons (by exact certified1537)
  apply certified_cons (by exact certified1538)
  apply certified_cons (by exact certified1538swap)
  apply certified_cons (by exact certified1539)
  apply certified_cons (by exact certified1540)
  apply certified_cons (by exact certified1540swap)
  apply certified_cons (by exact certified1541)
  apply certified_cons (by exact certified1542)
  apply certified_cons (by exact certified1542swap)
  apply certified_cons (by exact certified1543)
  apply certified_cons (by exact certified1544)
  apply certified_cons (by exact certified1544swap)
  apply certified_cons (by exact certified1545)
  apply certified_cons (by exact certified1546)
  apply certified_cons (by exact certified1546swap)
  apply certified_cons (by exact certified1547)
  apply certified_cons (by exact certified1548)
  apply certified_cons (by exact certified1548swap)
  apply certified_cons (by exact certified1549)
  simp
#print axioms certified_keys30
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
