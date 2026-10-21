/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0700
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0701
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0702
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0703
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0704
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0705
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0706
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0707
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0708
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0709
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0710
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0711
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0712
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0713
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0714
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0715
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0716
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0717
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0718
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0719
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0720
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0721
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0722
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0723
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0724
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0725
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0726
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0727
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0728
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0729
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0730
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0731
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0732
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0733
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0734
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0735
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0736
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0737
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0738
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0739
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0740
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0741
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0742
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0743
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0744
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0745
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0746
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0747
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0748
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0749
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys14 : ∀ k ∈ keys14, Certified k := by
  apply certified_cons (by exact certified0700)
  apply certified_cons (by exact certified0700swap)
  apply certified_cons (by exact certified0701)
  apply certified_cons (by exact certified0701swap)
  apply certified_cons (by exact certified0702)
  apply certified_cons (by exact certified0702swap)
  apply certified_cons (by exact certified0703)
  apply certified_cons (by exact certified0704)
  apply certified_cons (by exact certified0704swap)
  apply certified_cons (by exact certified0705)
  apply certified_cons (by exact certified0706)
  apply certified_cons (by exact certified0706swap)
  apply certified_cons (by exact certified0707)
  apply certified_cons (by exact certified0707swap)
  apply certified_cons (by exact certified0708)
  apply certified_cons (by exact certified0708swap)
  apply certified_cons (by exact certified0709)
  apply certified_cons (by exact certified0710)
  apply certified_cons (by exact certified0710swap)
  apply certified_cons (by exact certified0711)
  apply certified_cons (by exact certified0712)
  apply certified_cons (by exact certified0712swap)
  apply certified_cons (by exact certified0713)
  apply certified_cons (by exact certified0713swap)
  apply certified_cons (by exact certified0714)
  apply certified_cons (by exact certified0714swap)
  apply certified_cons (by exact certified0715)
  apply certified_cons (by exact certified0716)
  apply certified_cons (by exact certified0716swap)
  apply certified_cons (by exact certified0717)
  apply certified_cons (by exact certified0718)
  apply certified_cons (by exact certified0718swap)
  apply certified_cons (by exact certified0719)
  apply certified_cons (by exact certified0719swap)
  apply certified_cons (by exact certified0720)
  apply certified_cons (by exact certified0720swap)
  apply certified_cons (by exact certified0721)
  apply certified_cons (by exact certified0722)
  apply certified_cons (by exact certified0722swap)
  apply certified_cons (by exact certified0723)
  apply certified_cons (by exact certified0724)
  apply certified_cons (by exact certified0724swap)
  apply certified_cons (by exact certified0725)
  apply certified_cons (by exact certified0725swap)
  apply certified_cons (by exact certified0726)
  apply certified_cons (by exact certified0726swap)
  apply certified_cons (by exact certified0727)
  apply certified_cons (by exact certified0728)
  apply certified_cons (by exact certified0728swap)
  apply certified_cons (by exact certified0729)
  apply certified_cons (by exact certified0730)
  apply certified_cons (by exact certified0730swap)
  apply certified_cons (by exact certified0731)
  apply certified_cons (by exact certified0731swap)
  apply certified_cons (by exact certified0732)
  apply certified_cons (by exact certified0732swap)
  apply certified_cons (by exact certified0733)
  apply certified_cons (by exact certified0734)
  apply certified_cons (by exact certified0734swap)
  apply certified_cons (by exact certified0735)
  apply certified_cons (by exact certified0736)
  apply certified_cons (by exact certified0736swap)
  apply certified_cons (by exact certified0737)
  apply certified_cons (by exact certified0737swap)
  apply certified_cons (by exact certified0738)
  apply certified_cons (by exact certified0739)
  apply certified_cons (by exact certified0740)
  apply certified_cons (by exact certified0740swap)
  apply certified_cons (by exact certified0741)
  apply certified_cons (by exact certified0741swap)
  apply certified_cons (by exact certified0742)
  apply certified_cons (by exact certified0743)
  apply certified_cons (by exact certified0744)
  apply certified_cons (by exact certified0744swap)
  apply certified_cons (by exact certified0745)
  apply certified_cons (by exact certified0745swap)
  apply certified_cons (by exact certified0746)
  apply certified_cons (by exact certified0747)
  apply certified_cons (by exact certified0748)
  apply certified_cons (by exact certified0748swap)
  apply certified_cons (by exact certified0749)
  apply certified_cons (by exact certified0749swap)
  simp
#print axioms certified_keys14
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
