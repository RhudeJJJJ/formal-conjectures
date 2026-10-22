/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0550
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0551
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0552
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0553
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0554
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0555
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0556
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0557
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0558
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0559
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0560
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0561
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0562
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0563
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0564
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0565
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0566
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0567
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0568
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0569
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0570
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0571
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0572
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0573
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0574
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0575
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0576
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0577
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0578
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0579
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0580
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0581
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0582
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0583
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0584
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0585
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0586
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0587
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0588
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0589
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0590
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0591
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0592
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0593
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0594
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0595
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0596
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0597
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0598
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0599
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys011 : ∀ k ∈ keys011, Certified k := by
  apply certified_cons (by exact certified0550)
  apply certified_cons (by exact certified0551)
  apply certified_cons (by exact certified0552)
  apply certified_cons (by exact certified0553)
  apply certified_cons (by exact certified0554)
  apply certified_cons (by exact certified0555)
  apply certified_cons (by exact certified0556)
  apply certified_cons (by exact certified0557)
  apply certified_cons (by exact certified0558)
  apply certified_cons (by exact certified0559)
  apply certified_cons (by exact certified0560)
  apply certified_cons (by exact certified0561)
  apply certified_cons (by exact certified0562)
  apply certified_cons (by exact certified0563)
  apply certified_cons (by exact certified0564)
  apply certified_cons (by exact certified0565)
  apply certified_cons (by exact certified0566)
  apply certified_cons (by exact certified0567)
  apply certified_cons (by exact certified0568)
  apply certified_cons (by exact certified0569)
  apply certified_cons (by exact certified0570)
  apply certified_cons (by exact certified0571)
  apply certified_cons (by exact certified0572)
  apply certified_cons (by exact certified0573)
  apply certified_cons (by exact certified0574)
  apply certified_cons (by exact certified0575)
  apply certified_cons (by exact certified0576)
  apply certified_cons (by exact certified0577)
  apply certified_cons (by exact certified0578)
  apply certified_cons (by exact certified0579)
  apply certified_cons (by exact certified0580)
  apply certified_cons (by exact certified0581)
  apply certified_cons (by exact certified0582)
  apply certified_cons (by exact certified0583)
  apply certified_cons (by exact certified0584)
  apply certified_cons (by exact certified0585)
  apply certified_cons (by exact certified0586)
  apply certified_cons (by exact certified0587)
  apply certified_cons (by exact certified0588)
  apply certified_cons (by exact certified0589)
  apply certified_cons (by exact certified0590)
  apply certified_cons (by exact certified0591)
  apply certified_cons (by exact certified0592)
  apply certified_cons (by exact certified0593)
  apply certified_cons (by exact certified0594)
  apply certified_cons (by exact certified0595)
  apply certified_cons (by exact certified0596)
  apply certified_cons (by exact certified0597)
  apply certified_cons (by exact certified0598)
  apply certified_cons (by exact certified0599)
  simp
#print axioms certified_keys011
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
