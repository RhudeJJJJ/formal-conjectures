/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1700
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1701
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1702
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1703
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1704
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1705
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1706
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1707
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1708
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1709
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1710
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1711
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1712
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1713
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1714
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1715
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1716
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1717
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1718
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1719
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1720
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1721
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1722
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1723
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1724
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1725
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1726
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1727
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1728
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1729
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1730
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1731
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1732
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1733
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1734
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1735
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1736
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1737
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1738
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1739
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1740
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1741
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1742
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1743
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1744
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1745
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1746
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1747
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1748
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1749
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys034 : ∀ k ∈ keys034, Certified k := by
  apply certified_cons (by exact certified1700)
  apply certified_cons (by exact certified1700swap)
  apply certified_cons (by exact certified1701)
  apply certified_cons (by exact certified1701swap)
  apply certified_cons (by exact certified1702)
  apply certified_cons (by exact certified1702swap)
  apply certified_cons (by exact certified1703)
  apply certified_cons (by exact certified1703swap)
  apply certified_cons (by exact certified1704)
  apply certified_cons (by exact certified1704swap)
  apply certified_cons (by exact certified1705)
  apply certified_cons (by exact certified1705swap)
  apply certified_cons (by exact certified1706)
  apply certified_cons (by exact certified1706swap)
  apply certified_cons (by exact certified1707)
  apply certified_cons (by exact certified1707swap)
  apply certified_cons (by exact certified1708)
  apply certified_cons (by exact certified1708swap)
  apply certified_cons (by exact certified1709)
  apply certified_cons (by exact certified1709swap)
  apply certified_cons (by exact certified1710)
  apply certified_cons (by exact certified1710swap)
  apply certified_cons (by exact certified1711)
  apply certified_cons (by exact certified1711swap)
  apply certified_cons (by exact certified1712)
  apply certified_cons (by exact certified1712swap)
  apply certified_cons (by exact certified1713)
  apply certified_cons (by exact certified1713swap)
  apply certified_cons (by exact certified1714)
  apply certified_cons (by exact certified1714swap)
  apply certified_cons (by exact certified1715)
  apply certified_cons (by exact certified1715swap)
  apply certified_cons (by exact certified1716)
  apply certified_cons (by exact certified1716swap)
  apply certified_cons (by exact certified1717)
  apply certified_cons (by exact certified1717swap)
  apply certified_cons (by exact certified1718)
  apply certified_cons (by exact certified1718swap)
  apply certified_cons (by exact certified1719)
  apply certified_cons (by exact certified1719swap)
  apply certified_cons (by exact certified1720)
  apply certified_cons (by exact certified1720swap)
  apply certified_cons (by exact certified1721)
  apply certified_cons (by exact certified1721swap)
  apply certified_cons (by exact certified1722)
  apply certified_cons (by exact certified1722swap)
  apply certified_cons (by exact certified1723)
  apply certified_cons (by exact certified1723swap)
  apply certified_cons (by exact certified1724)
  apply certified_cons (by exact certified1724swap)
  apply certified_cons (by exact certified1725)
  apply certified_cons (by exact certified1725swap)
  apply certified_cons (by exact certified1726)
  apply certified_cons (by exact certified1726swap)
  apply certified_cons (by exact certified1727)
  apply certified_cons (by exact certified1727swap)
  apply certified_cons (by exact certified1728)
  apply certified_cons (by exact certified1728swap)
  apply certified_cons (by exact certified1729)
  apply certified_cons (by exact certified1729swap)
  apply certified_cons (by exact certified1730)
  apply certified_cons (by exact certified1730swap)
  apply certified_cons (by exact certified1731)
  apply certified_cons (by exact certified1731swap)
  apply certified_cons (by exact certified1732)
  apply certified_cons (by exact certified1732swap)
  apply certified_cons (by exact certified1733)
  apply certified_cons (by exact certified1733swap)
  apply certified_cons (by exact certified1734)
  apply certified_cons (by exact certified1734swap)
  apply certified_cons (by exact certified1735)
  apply certified_cons (by exact certified1735swap)
  apply certified_cons (by exact certified1736)
  apply certified_cons (by exact certified1736swap)
  apply certified_cons (by exact certified1737)
  apply certified_cons (by exact certified1737swap)
  apply certified_cons (by exact certified1738)
  apply certified_cons (by exact certified1738swap)
  apply certified_cons (by exact certified1739)
  apply certified_cons (by exact certified1739swap)
  apply certified_cons (by exact certified1740)
  apply certified_cons (by exact certified1740swap)
  apply certified_cons (by exact certified1741)
  apply certified_cons (by exact certified1741swap)
  apply certified_cons (by exact certified1742)
  apply certified_cons (by exact certified1742swap)
  apply certified_cons (by exact certified1743)
  apply certified_cons (by exact certified1743swap)
  apply certified_cons (by exact certified1744)
  apply certified_cons (by exact certified1744swap)
  apply certified_cons (by exact certified1745)
  apply certified_cons (by exact certified1745swap)
  apply certified_cons (by exact certified1746)
  apply certified_cons (by exact certified1746swap)
  apply certified_cons (by exact certified1747)
  apply certified_cons (by exact certified1747swap)
  apply certified_cons (by exact certified1748)
  apply certified_cons (by exact certified1748swap)
  apply certified_cons (by exact certified1749)
  apply certified_cons (by exact certified1749swap)
  simp
#print axioms certified_keys034
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
