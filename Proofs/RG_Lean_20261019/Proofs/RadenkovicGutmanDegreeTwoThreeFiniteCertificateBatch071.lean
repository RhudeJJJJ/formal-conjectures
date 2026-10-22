/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3550
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3551
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3552
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3553
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3554
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3555
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3556
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3557
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3558
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3559
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3560
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3561
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3562
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3563
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3564
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3565
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3566
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3567
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3568
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3569
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3570
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3571
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3572
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3573
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3574
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3575
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3576
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3577
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3578
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3579
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3580
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3581
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3582
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3583
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3584
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3585
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3586
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3587
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3588
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3589
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3590
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3591
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3592
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3593
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3594
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3595
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3596
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3597
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3598
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3599
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys071 : ∀ k ∈ keys071, Certified k := by
  apply certified_cons (by exact certified3550)
  apply certified_cons (by exact certified3550swap)
  apply certified_cons (by exact certified3551)
  apply certified_cons (by exact certified3551swap)
  apply certified_cons (by exact certified3552)
  apply certified_cons (by exact certified3552swap)
  apply certified_cons (by exact certified3553)
  apply certified_cons (by exact certified3553swap)
  apply certified_cons (by exact certified3554)
  apply certified_cons (by exact certified3554swap)
  apply certified_cons (by exact certified3555)
  apply certified_cons (by exact certified3555swap)
  apply certified_cons (by exact certified3556)
  apply certified_cons (by exact certified3556swap)
  apply certified_cons (by exact certified3557)
  apply certified_cons (by exact certified3557swap)
  apply certified_cons (by exact certified3558)
  apply certified_cons (by exact certified3558swap)
  apply certified_cons (by exact certified3559)
  apply certified_cons (by exact certified3559swap)
  apply certified_cons (by exact certified3560)
  apply certified_cons (by exact certified3560swap)
  apply certified_cons (by exact certified3561)
  apply certified_cons (by exact certified3561swap)
  apply certified_cons (by exact certified3562)
  apply certified_cons (by exact certified3562swap)
  apply certified_cons (by exact certified3563)
  apply certified_cons (by exact certified3563swap)
  apply certified_cons (by exact certified3564)
  apply certified_cons (by exact certified3564swap)
  apply certified_cons (by exact certified3565)
  apply certified_cons (by exact certified3565swap)
  apply certified_cons (by exact certified3566)
  apply certified_cons (by exact certified3566swap)
  apply certified_cons (by exact certified3567)
  apply certified_cons (by exact certified3567swap)
  apply certified_cons (by exact certified3568)
  apply certified_cons (by exact certified3568swap)
  apply certified_cons (by exact certified3569)
  apply certified_cons (by exact certified3569swap)
  apply certified_cons (by exact certified3570)
  apply certified_cons (by exact certified3570swap)
  apply certified_cons (by exact certified3571)
  apply certified_cons (by exact certified3571swap)
  apply certified_cons (by exact certified3572)
  apply certified_cons (by exact certified3572swap)
  apply certified_cons (by exact certified3573)
  apply certified_cons (by exact certified3573swap)
  apply certified_cons (by exact certified3574)
  apply certified_cons (by exact certified3574swap)
  apply certified_cons (by exact certified3575)
  apply certified_cons (by exact certified3575swap)
  apply certified_cons (by exact certified3576)
  apply certified_cons (by exact certified3576swap)
  apply certified_cons (by exact certified3577)
  apply certified_cons (by exact certified3577swap)
  apply certified_cons (by exact certified3578)
  apply certified_cons (by exact certified3578swap)
  apply certified_cons (by exact certified3579)
  apply certified_cons (by exact certified3579swap)
  apply certified_cons (by exact certified3580)
  apply certified_cons (by exact certified3580swap)
  apply certified_cons (by exact certified3581)
  apply certified_cons (by exact certified3581swap)
  apply certified_cons (by exact certified3582)
  apply certified_cons (by exact certified3582swap)
  apply certified_cons (by exact certified3583)
  apply certified_cons (by exact certified3583swap)
  apply certified_cons (by exact certified3584)
  apply certified_cons (by exact certified3584swap)
  apply certified_cons (by exact certified3585)
  apply certified_cons (by exact certified3585swap)
  apply certified_cons (by exact certified3586)
  apply certified_cons (by exact certified3586swap)
  apply certified_cons (by exact certified3587)
  apply certified_cons (by exact certified3587swap)
  apply certified_cons (by exact certified3588)
  apply certified_cons (by exact certified3588swap)
  apply certified_cons (by exact certified3589)
  apply certified_cons (by exact certified3589swap)
  apply certified_cons (by exact certified3590)
  apply certified_cons (by exact certified3590swap)
  apply certified_cons (by exact certified3591)
  apply certified_cons (by exact certified3591swap)
  apply certified_cons (by exact certified3592)
  apply certified_cons (by exact certified3592swap)
  apply certified_cons (by exact certified3593)
  apply certified_cons (by exact certified3593swap)
  apply certified_cons (by exact certified3594)
  apply certified_cons (by exact certified3594swap)
  apply certified_cons (by exact certified3595)
  apply certified_cons (by exact certified3595swap)
  apply certified_cons (by exact certified3596)
  apply certified_cons (by exact certified3596swap)
  apply certified_cons (by exact certified3597)
  apply certified_cons (by exact certified3597swap)
  apply certified_cons (by exact certified3598)
  apply certified_cons (by exact certified3598swap)
  apply certified_cons (by exact certified3599)
  apply certified_cons (by exact certified3599swap)
  simp
#print axioms certified_keys071
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
