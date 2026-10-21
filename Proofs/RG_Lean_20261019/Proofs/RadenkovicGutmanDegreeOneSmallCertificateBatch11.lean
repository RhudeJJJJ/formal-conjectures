/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0550
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0551
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0552
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0553
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0554
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0555
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0556
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0557
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0558
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0559
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0560
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0561
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0562
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0563
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0564
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0565
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0566
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0567
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0568
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0569
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0570
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0571
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0572
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0573
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0574
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0575
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0576
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0577
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0578
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0579
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0580
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0581
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0582
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0583
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0584
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0585
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0586
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0587
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0588
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0589
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0590
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0591
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0592
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0593
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0594
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0595
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0596
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0597
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0598
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0599
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys11 : ∀ k ∈ keys11, Certified k := by
  apply certified_cons (by exact certified0550)
  apply certified_cons (by exact certified0550swap)
  apply certified_cons (by exact certified0551)
  apply certified_cons (by exact certified0551swap)
  apply certified_cons (by exact certified0552)
  apply certified_cons (by exact certified0552swap)
  apply certified_cons (by exact certified0553)
  apply certified_cons (by exact certified0554)
  apply certified_cons (by exact certified0554swap)
  apply certified_cons (by exact certified0555)
  apply certified_cons (by exact certified0556)
  apply certified_cons (by exact certified0556swap)
  apply certified_cons (by exact certified0557)
  apply certified_cons (by exact certified0557swap)
  apply certified_cons (by exact certified0558)
  apply certified_cons (by exact certified0558swap)
  apply certified_cons (by exact certified0559)
  apply certified_cons (by exact certified0560)
  apply certified_cons (by exact certified0560swap)
  apply certified_cons (by exact certified0561)
  apply certified_cons (by exact certified0562)
  apply certified_cons (by exact certified0562swap)
  apply certified_cons (by exact certified0563)
  apply certified_cons (by exact certified0563swap)
  apply certified_cons (by exact certified0564)
  apply certified_cons (by exact certified0564swap)
  apply certified_cons (by exact certified0565)
  apply certified_cons (by exact certified0566)
  apply certified_cons (by exact certified0566swap)
  apply certified_cons (by exact certified0567)
  apply certified_cons (by exact certified0568)
  apply certified_cons (by exact certified0568swap)
  apply certified_cons (by exact certified0569)
  apply certified_cons (by exact certified0569swap)
  apply certified_cons (by exact certified0570)
  apply certified_cons (by exact certified0570swap)
  apply certified_cons (by exact certified0571)
  apply certified_cons (by exact certified0572)
  apply certified_cons (by exact certified0572swap)
  apply certified_cons (by exact certified0573)
  apply certified_cons (by exact certified0574)
  apply certified_cons (by exact certified0574swap)
  apply certified_cons (by exact certified0575)
  apply certified_cons (by exact certified0575swap)
  apply certified_cons (by exact certified0576)
  apply certified_cons (by exact certified0576swap)
  apply certified_cons (by exact certified0577)
  apply certified_cons (by exact certified0578)
  apply certified_cons (by exact certified0578swap)
  apply certified_cons (by exact certified0579)
  apply certified_cons (by exact certified0580)
  apply certified_cons (by exact certified0580swap)
  apply certified_cons (by exact certified0581)
  apply certified_cons (by exact certified0581swap)
  apply certified_cons (by exact certified0582)
  apply certified_cons (by exact certified0582swap)
  apply certified_cons (by exact certified0583)
  apply certified_cons (by exact certified0584)
  apply certified_cons (by exact certified0584swap)
  apply certified_cons (by exact certified0585)
  apply certified_cons (by exact certified0586)
  apply certified_cons (by exact certified0586swap)
  apply certified_cons (by exact certified0587)
  apply certified_cons (by exact certified0587swap)
  apply certified_cons (by exact certified0588)
  apply certified_cons (by exact certified0588swap)
  apply certified_cons (by exact certified0589)
  apply certified_cons (by exact certified0590)
  apply certified_cons (by exact certified0590swap)
  apply certified_cons (by exact certified0591)
  apply certified_cons (by exact certified0592)
  apply certified_cons (by exact certified0592swap)
  apply certified_cons (by exact certified0593)
  apply certified_cons (by exact certified0593swap)
  apply certified_cons (by exact certified0594)
  apply certified_cons (by exact certified0594swap)
  apply certified_cons (by exact certified0595)
  apply certified_cons (by exact certified0596)
  apply certified_cons (by exact certified0596swap)
  apply certified_cons (by exact certified0597)
  apply certified_cons (by exact certified0598)
  apply certified_cons (by exact certified0598swap)
  apply certified_cons (by exact certified0599)
  apply certified_cons (by exact certified0599swap)
  simp
#print axioms certified_keys11
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
