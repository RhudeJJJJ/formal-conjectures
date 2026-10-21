/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1700
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1701
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1702
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1703
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1704
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1705
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1706
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1707
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1708
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1709
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1710
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1711
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1712
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1713
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1714
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1715
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1716
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1717
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1718
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1719
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1720
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1721
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1722
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1723
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1724
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1725
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1726
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1727
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1728
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1729
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1730
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1731
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1732
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1733
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1734
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1735
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1736
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1737
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1738
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1739
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1740
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1741
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1742
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1743
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1744
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1745
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1746
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1747
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1748
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1749
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys34 : ∀ k ∈ keys34, Certified k := by
  apply certified_cons (by exact certified1700)
  apply certified_cons (by exact certified1700swap)
  apply certified_cons (by exact certified1701)
  apply certified_cons (by exact certified1702)
  apply certified_cons (by exact certified1702swap)
  apply certified_cons (by exact certified1703)
  apply certified_cons (by exact certified1704)
  apply certified_cons (by exact certified1704swap)
  apply certified_cons (by exact certified1705)
  apply certified_cons (by exact certified1706)
  apply certified_cons (by exact certified1706swap)
  apply certified_cons (by exact certified1707)
  apply certified_cons (by exact certified1708)
  apply certified_cons (by exact certified1708swap)
  apply certified_cons (by exact certified1709)
  apply certified_cons (by exact certified1710)
  apply certified_cons (by exact certified1710swap)
  apply certified_cons (by exact certified1711)
  apply certified_cons (by exact certified1712)
  apply certified_cons (by exact certified1712swap)
  apply certified_cons (by exact certified1713)
  apply certified_cons (by exact certified1714)
  apply certified_cons (by exact certified1714swap)
  apply certified_cons (by exact certified1715)
  apply certified_cons (by exact certified1716)
  apply certified_cons (by exact certified1716swap)
  apply certified_cons (by exact certified1717)
  apply certified_cons (by exact certified1718)
  apply certified_cons (by exact certified1718swap)
  apply certified_cons (by exact certified1719)
  apply certified_cons (by exact certified1720)
  apply certified_cons (by exact certified1720swap)
  apply certified_cons (by exact certified1721)
  apply certified_cons (by exact certified1722)
  apply certified_cons (by exact certified1722swap)
  apply certified_cons (by exact certified1723)
  apply certified_cons (by exact certified1724)
  apply certified_cons (by exact certified1724swap)
  apply certified_cons (by exact certified1725)
  apply certified_cons (by exact certified1726)
  apply certified_cons (by exact certified1726swap)
  apply certified_cons (by exact certified1727)
  apply certified_cons (by exact certified1728)
  apply certified_cons (by exact certified1728swap)
  apply certified_cons (by exact certified1729)
  apply certified_cons (by exact certified1730)
  apply certified_cons (by exact certified1730swap)
  apply certified_cons (by exact certified1731)
  apply certified_cons (by exact certified1732)
  apply certified_cons (by exact certified1732swap)
  apply certified_cons (by exact certified1733)
  apply certified_cons (by exact certified1734)
  apply certified_cons (by exact certified1734swap)
  apply certified_cons (by exact certified1735)
  apply certified_cons (by exact certified1736)
  apply certified_cons (by exact certified1736swap)
  apply certified_cons (by exact certified1737)
  apply certified_cons (by exact certified1738)
  apply certified_cons (by exact certified1738swap)
  apply certified_cons (by exact certified1739)
  apply certified_cons (by exact certified1740)
  apply certified_cons (by exact certified1740swap)
  apply certified_cons (by exact certified1741)
  apply certified_cons (by exact certified1742)
  apply certified_cons (by exact certified1742swap)
  apply certified_cons (by exact certified1743)
  apply certified_cons (by exact certified1744)
  apply certified_cons (by exact certified1744swap)
  apply certified_cons (by exact certified1745)
  apply certified_cons (by exact certified1746)
  apply certified_cons (by exact certified1746swap)
  apply certified_cons (by exact certified1747)
  apply certified_cons (by exact certified1748)
  apply certified_cons (by exact certified1748swap)
  apply certified_cons (by exact certified1749)
  simp
#print axioms certified_keys34
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
