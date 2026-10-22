/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3700
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3701
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3702
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3703
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3704
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3705
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3706
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3707
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3708
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3709
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3710
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3711
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3712
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3713
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3714
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3715
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3716
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3717
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3718
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3719
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3720
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3721
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3722
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3723
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3724
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3725
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3726
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3727
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3728
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3729
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3730
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3731
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3732
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3733
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3734
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3735
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3736
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3737
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3738
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3739
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3740
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3741
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3742
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3743
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3744
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3745
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3746
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3747
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3748
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3749
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys074 : ∀ k ∈ keys074, Certified k := by
  apply certified_cons (by exact certified3700)
  apply certified_cons (by exact certified3700swap)
  apply certified_cons (by exact certified3701)
  apply certified_cons (by exact certified3701swap)
  apply certified_cons (by exact certified3702)
  apply certified_cons (by exact certified3702swap)
  apply certified_cons (by exact certified3703)
  apply certified_cons (by exact certified3703swap)
  apply certified_cons (by exact certified3704)
  apply certified_cons (by exact certified3704swap)
  apply certified_cons (by exact certified3705)
  apply certified_cons (by exact certified3705swap)
  apply certified_cons (by exact certified3706)
  apply certified_cons (by exact certified3706swap)
  apply certified_cons (by exact certified3707)
  apply certified_cons (by exact certified3707swap)
  apply certified_cons (by exact certified3708)
  apply certified_cons (by exact certified3708swap)
  apply certified_cons (by exact certified3709)
  apply certified_cons (by exact certified3709swap)
  apply certified_cons (by exact certified3710)
  apply certified_cons (by exact certified3710swap)
  apply certified_cons (by exact certified3711)
  apply certified_cons (by exact certified3711swap)
  apply certified_cons (by exact certified3712)
  apply certified_cons (by exact certified3712swap)
  apply certified_cons (by exact certified3713)
  apply certified_cons (by exact certified3713swap)
  apply certified_cons (by exact certified3714)
  apply certified_cons (by exact certified3714swap)
  apply certified_cons (by exact certified3715)
  apply certified_cons (by exact certified3715swap)
  apply certified_cons (by exact certified3716)
  apply certified_cons (by exact certified3716swap)
  apply certified_cons (by exact certified3717)
  apply certified_cons (by exact certified3717swap)
  apply certified_cons (by exact certified3718)
  apply certified_cons (by exact certified3718swap)
  apply certified_cons (by exact certified3719)
  apply certified_cons (by exact certified3719swap)
  apply certified_cons (by exact certified3720)
  apply certified_cons (by exact certified3720swap)
  apply certified_cons (by exact certified3721)
  apply certified_cons (by exact certified3721swap)
  apply certified_cons (by exact certified3722)
  apply certified_cons (by exact certified3722swap)
  apply certified_cons (by exact certified3723)
  apply certified_cons (by exact certified3723swap)
  apply certified_cons (by exact certified3724)
  apply certified_cons (by exact certified3724swap)
  apply certified_cons (by exact certified3725)
  apply certified_cons (by exact certified3725swap)
  apply certified_cons (by exact certified3726)
  apply certified_cons (by exact certified3726swap)
  apply certified_cons (by exact certified3727)
  apply certified_cons (by exact certified3727swap)
  apply certified_cons (by exact certified3728)
  apply certified_cons (by exact certified3728swap)
  apply certified_cons (by exact certified3729)
  apply certified_cons (by exact certified3729swap)
  apply certified_cons (by exact certified3730)
  apply certified_cons (by exact certified3730swap)
  apply certified_cons (by exact certified3731)
  apply certified_cons (by exact certified3731swap)
  apply certified_cons (by exact certified3732)
  apply certified_cons (by exact certified3732swap)
  apply certified_cons (by exact certified3733)
  apply certified_cons (by exact certified3733swap)
  apply certified_cons (by exact certified3734)
  apply certified_cons (by exact certified3734swap)
  apply certified_cons (by exact certified3735)
  apply certified_cons (by exact certified3735swap)
  apply certified_cons (by exact certified3736)
  apply certified_cons (by exact certified3736swap)
  apply certified_cons (by exact certified3737)
  apply certified_cons (by exact certified3737swap)
  apply certified_cons (by exact certified3738)
  apply certified_cons (by exact certified3738swap)
  apply certified_cons (by exact certified3739)
  apply certified_cons (by exact certified3739swap)
  apply certified_cons (by exact certified3740)
  apply certified_cons (by exact certified3740swap)
  apply certified_cons (by exact certified3741)
  apply certified_cons (by exact certified3741swap)
  apply certified_cons (by exact certified3742)
  apply certified_cons (by exact certified3742swap)
  apply certified_cons (by exact certified3743)
  apply certified_cons (by exact certified3743swap)
  apply certified_cons (by exact certified3744)
  apply certified_cons (by exact certified3744swap)
  apply certified_cons (by exact certified3745)
  apply certified_cons (by exact certified3746)
  apply certified_cons (by exact certified3747)
  apply certified_cons (by exact certified3748)
  apply certified_cons (by exact certified3749)
  simp
#print axioms certified_keys074
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
