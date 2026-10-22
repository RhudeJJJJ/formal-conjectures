/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0700
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0701
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0702
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0703
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0704
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0705
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0706
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0707
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0708
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0709
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0710
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0711
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0712
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0713
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0714
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0715
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0716
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0717
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0718
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0719
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0720
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0721
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0722
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0723
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0724
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0725
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0726
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0727
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0728
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0729
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0730
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0731
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0732
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0733
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0734
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0735
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0736
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0737
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0738
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0739
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0740
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0741
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0742
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0743
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0744
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0745
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0746
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0747
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0748
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0749
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys014 : ∀ k ∈ keys014, Certified k := by
  apply certified_cons (by exact certified0700)
  apply certified_cons (by exact certified0701)
  apply certified_cons (by exact certified0702)
  apply certified_cons (by exact certified0703)
  apply certified_cons (by exact certified0704)
  apply certified_cons (by exact certified0705)
  apply certified_cons (by exact certified0706)
  apply certified_cons (by exact certified0707)
  apply certified_cons (by exact certified0708)
  apply certified_cons (by exact certified0709)
  apply certified_cons (by exact certified0710)
  apply certified_cons (by exact certified0711)
  apply certified_cons (by exact certified0712)
  apply certified_cons (by exact certified0713)
  apply certified_cons (by exact certified0714)
  apply certified_cons (by exact certified0715)
  apply certified_cons (by exact certified0716)
  apply certified_cons (by exact certified0717)
  apply certified_cons (by exact certified0718)
  apply certified_cons (by exact certified0719)
  apply certified_cons (by exact certified0720)
  apply certified_cons (by exact certified0721)
  apply certified_cons (by exact certified0722)
  apply certified_cons (by exact certified0723)
  apply certified_cons (by exact certified0724)
  apply certified_cons (by exact certified0725)
  apply certified_cons (by exact certified0726)
  apply certified_cons (by exact certified0727)
  apply certified_cons (by exact certified0728)
  apply certified_cons (by exact certified0729)
  apply certified_cons (by exact certified0730)
  apply certified_cons (by exact certified0731)
  apply certified_cons (by exact certified0732)
  apply certified_cons (by exact certified0733)
  apply certified_cons (by exact certified0734)
  apply certified_cons (by exact certified0735)
  apply certified_cons (by exact certified0736)
  apply certified_cons (by exact certified0737)
  apply certified_cons (by exact certified0738)
  apply certified_cons (by exact certified0739)
  apply certified_cons (by exact certified0740)
  apply certified_cons (by exact certified0741)
  apply certified_cons (by exact certified0742)
  apply certified_cons (by exact certified0743)
  apply certified_cons (by exact certified0744)
  apply certified_cons (by exact certified0745)
  apply certified_cons (by exact certified0746)
  apply certified_cons (by exact certified0747)
  apply certified_cons (by exact certified0748)
  apply certified_cons (by exact certified0749)
  simp
#print axioms certified_keys014
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
