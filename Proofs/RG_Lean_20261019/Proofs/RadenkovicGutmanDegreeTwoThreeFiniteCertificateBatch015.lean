/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0750
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0751
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0752
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0753
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0754
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0755
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0756
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0757
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0758
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0759
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0760
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0761
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0762
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0763
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0764
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0765
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0766
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0767
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0768
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0769
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0770
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0771
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0772
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0773
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0774
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0775
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0776
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0777
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0778
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0779
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0780
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0781
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0782
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0783
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0784
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0785
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0786
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0787
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0788
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0789
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0790
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0791
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0792
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0793
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0794
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0795
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0796
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0797
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0798
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0799
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys015 : ∀ k ∈ keys015, Certified k := by
  apply certified_cons (by exact certified0750)
  apply certified_cons (by exact certified0751)
  apply certified_cons (by exact certified0752)
  apply certified_cons (by exact certified0753)
  apply certified_cons (by exact certified0754)
  apply certified_cons (by exact certified0755)
  apply certified_cons (by exact certified0756)
  apply certified_cons (by exact certified0757)
  apply certified_cons (by exact certified0758)
  apply certified_cons (by exact certified0759)
  apply certified_cons (by exact certified0760)
  apply certified_cons (by exact certified0761)
  apply certified_cons (by exact certified0762)
  apply certified_cons (by exact certified0763)
  apply certified_cons (by exact certified0764)
  apply certified_cons (by exact certified0765)
  apply certified_cons (by exact certified0766)
  apply certified_cons (by exact certified0767)
  apply certified_cons (by exact certified0768)
  apply certified_cons (by exact certified0769)
  apply certified_cons (by exact certified0770)
  apply certified_cons (by exact certified0771)
  apply certified_cons (by exact certified0772)
  apply certified_cons (by exact certified0773)
  apply certified_cons (by exact certified0774)
  apply certified_cons (by exact certified0775)
  apply certified_cons (by exact certified0776)
  apply certified_cons (by exact certified0777)
  apply certified_cons (by exact certified0778)
  apply certified_cons (by exact certified0779)
  apply certified_cons (by exact certified0780)
  apply certified_cons (by exact certified0781)
  apply certified_cons (by exact certified0782)
  apply certified_cons (by exact certified0783)
  apply certified_cons (by exact certified0784)
  apply certified_cons (by exact certified0785)
  apply certified_cons (by exact certified0786)
  apply certified_cons (by exact certified0787)
  apply certified_cons (by exact certified0788)
  apply certified_cons (by exact certified0789)
  apply certified_cons (by exact certified0790)
  apply certified_cons (by exact certified0791)
  apply certified_cons (by exact certified0792)
  apply certified_cons (by exact certified0793)
  apply certified_cons (by exact certified0794)
  apply certified_cons (by exact certified0795)
  apply certified_cons (by exact certified0796)
  apply certified_cons (by exact certified0797)
  apply certified_cons (by exact certified0798)
  apply certified_cons (by exact certified0799)
  simp
#print axioms certified_keys015
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
