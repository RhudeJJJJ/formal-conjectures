/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0750
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0751
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0752
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0753
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0754
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0755
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0756
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0757
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0758
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0759
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0760
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0761
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0762
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0763
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0764
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0765
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0766
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0767
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0768
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0769
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0770
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0771
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0772
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0773
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0774
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0775
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0776
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0777
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0778
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0779
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0780
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0781
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0782
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0783
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0784
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0785
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0786
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0787
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0788
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0789
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0790
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0791
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0792
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0793
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0794
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0795
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0796
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0797
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0798
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0799
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys15 : ∀ k ∈ keys15, Certified k := by
  apply certified_cons (by exact certified0750)
  apply certified_cons (by exact certified0751)
  apply certified_cons (by exact certified0752)
  apply certified_cons (by exact certified0752swap)
  apply certified_cons (by exact certified0753)
  apply certified_cons (by exact certified0753swap)
  apply certified_cons (by exact certified0754)
  apply certified_cons (by exact certified0755)
  apply certified_cons (by exact certified0756)
  apply certified_cons (by exact certified0756swap)
  apply certified_cons (by exact certified0757)
  apply certified_cons (by exact certified0757swap)
  apply certified_cons (by exact certified0758)
  apply certified_cons (by exact certified0759)
  apply certified_cons (by exact certified0760)
  apply certified_cons (by exact certified0760swap)
  apply certified_cons (by exact certified0761)
  apply certified_cons (by exact certified0761swap)
  apply certified_cons (by exact certified0762)
  apply certified_cons (by exact certified0763)
  apply certified_cons (by exact certified0764)
  apply certified_cons (by exact certified0764swap)
  apply certified_cons (by exact certified0765)
  apply certified_cons (by exact certified0765swap)
  apply certified_cons (by exact certified0766)
  apply certified_cons (by exact certified0767)
  apply certified_cons (by exact certified0768)
  apply certified_cons (by exact certified0768swap)
  apply certified_cons (by exact certified0769)
  apply certified_cons (by exact certified0769swap)
  apply certified_cons (by exact certified0770)
  apply certified_cons (by exact certified0771)
  apply certified_cons (by exact certified0772)
  apply certified_cons (by exact certified0772swap)
  apply certified_cons (by exact certified0773)
  apply certified_cons (by exact certified0773swap)
  apply certified_cons (by exact certified0774)
  apply certified_cons (by exact certified0775)
  apply certified_cons (by exact certified0776)
  apply certified_cons (by exact certified0776swap)
  apply certified_cons (by exact certified0777)
  apply certified_cons (by exact certified0777swap)
  apply certified_cons (by exact certified0778)
  apply certified_cons (by exact certified0779)
  apply certified_cons (by exact certified0780)
  apply certified_cons (by exact certified0780swap)
  apply certified_cons (by exact certified0781)
  apply certified_cons (by exact certified0781swap)
  apply certified_cons (by exact certified0782)
  apply certified_cons (by exact certified0783)
  apply certified_cons (by exact certified0784)
  apply certified_cons (by exact certified0784swap)
  apply certified_cons (by exact certified0785)
  apply certified_cons (by exact certified0785swap)
  apply certified_cons (by exact certified0786)
  apply certified_cons (by exact certified0787)
  apply certified_cons (by exact certified0788)
  apply certified_cons (by exact certified0788swap)
  apply certified_cons (by exact certified0789)
  apply certified_cons (by exact certified0789swap)
  apply certified_cons (by exact certified0790)
  apply certified_cons (by exact certified0791)
  apply certified_cons (by exact certified0792)
  apply certified_cons (by exact certified0792swap)
  apply certified_cons (by exact certified0793)
  apply certified_cons (by exact certified0793swap)
  apply certified_cons (by exact certified0794)
  apply certified_cons (by exact certified0795)
  apply certified_cons (by exact certified0796)
  apply certified_cons (by exact certified0796swap)
  apply certified_cons (by exact certified0797)
  apply certified_cons (by exact certified0797swap)
  apply certified_cons (by exact certified0798)
  apply certified_cons (by exact certified0799)
  simp
#print axioms certified_keys15
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
