/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3900
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3901
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3902
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3903
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3904
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3905
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3906
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3907
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3908
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3909
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3910
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3911
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3912
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3913
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3914
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3915
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3916
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3917
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3918
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3919
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3920
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3921
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3922
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3923
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3924
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3925
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3926
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3927
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3928
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3929
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3930
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3931
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3932
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3933
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3934
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3935
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3936
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3937
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3938
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3939
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3940
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3941
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3942
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3943
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3944
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3945
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3946
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3947
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3948
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3949
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys078 : ∀ k ∈ keys078, Certified k := by
  apply certified_cons (by exact certified3900)
  apply certified_cons (by exact certified3900swap)
  apply certified_cons (by exact certified3901)
  apply certified_cons (by exact certified3901swap)
  apply certified_cons (by exact certified3902)
  apply certified_cons (by exact certified3902swap)
  apply certified_cons (by exact certified3903)
  apply certified_cons (by exact certified3903swap)
  apply certified_cons (by exact certified3904)
  apply certified_cons (by exact certified3904swap)
  apply certified_cons (by exact certified3905)
  apply certified_cons (by exact certified3905swap)
  apply certified_cons (by exact certified3906)
  apply certified_cons (by exact certified3906swap)
  apply certified_cons (by exact certified3907)
  apply certified_cons (by exact certified3907swap)
  apply certified_cons (by exact certified3908)
  apply certified_cons (by exact certified3908swap)
  apply certified_cons (by exact certified3909)
  apply certified_cons (by exact certified3909swap)
  apply certified_cons (by exact certified3910)
  apply certified_cons (by exact certified3910swap)
  apply certified_cons (by exact certified3911)
  apply certified_cons (by exact certified3911swap)
  apply certified_cons (by exact certified3912)
  apply certified_cons (by exact certified3912swap)
  apply certified_cons (by exact certified3913)
  apply certified_cons (by exact certified3913swap)
  apply certified_cons (by exact certified3914)
  apply certified_cons (by exact certified3914swap)
  apply certified_cons (by exact certified3915)
  apply certified_cons (by exact certified3915swap)
  apply certified_cons (by exact certified3916)
  apply certified_cons (by exact certified3916swap)
  apply certified_cons (by exact certified3917)
  apply certified_cons (by exact certified3917swap)
  apply certified_cons (by exact certified3918)
  apply certified_cons (by exact certified3918swap)
  apply certified_cons (by exact certified3919)
  apply certified_cons (by exact certified3919swap)
  apply certified_cons (by exact certified3920)
  apply certified_cons (by exact certified3920swap)
  apply certified_cons (by exact certified3921)
  apply certified_cons (by exact certified3921swap)
  apply certified_cons (by exact certified3922)
  apply certified_cons (by exact certified3922swap)
  apply certified_cons (by exact certified3923)
  apply certified_cons (by exact certified3923swap)
  apply certified_cons (by exact certified3924)
  apply certified_cons (by exact certified3924swap)
  apply certified_cons (by exact certified3925)
  apply certified_cons (by exact certified3925swap)
  apply certified_cons (by exact certified3926)
  apply certified_cons (by exact certified3926swap)
  apply certified_cons (by exact certified3927)
  apply certified_cons (by exact certified3927swap)
  apply certified_cons (by exact certified3928)
  apply certified_cons (by exact certified3928swap)
  apply certified_cons (by exact certified3929)
  apply certified_cons (by exact certified3929swap)
  apply certified_cons (by exact certified3930)
  apply certified_cons (by exact certified3930swap)
  apply certified_cons (by exact certified3931)
  apply certified_cons (by exact certified3931swap)
  apply certified_cons (by exact certified3932)
  apply certified_cons (by exact certified3932swap)
  apply certified_cons (by exact certified3933)
  apply certified_cons (by exact certified3933swap)
  apply certified_cons (by exact certified3934)
  apply certified_cons (by exact certified3934swap)
  apply certified_cons (by exact certified3935)
  apply certified_cons (by exact certified3935swap)
  apply certified_cons (by exact certified3936)
  apply certified_cons (by exact certified3936swap)
  apply certified_cons (by exact certified3937)
  apply certified_cons (by exact certified3937swap)
  apply certified_cons (by exact certified3938)
  apply certified_cons (by exact certified3938swap)
  apply certified_cons (by exact certified3939)
  apply certified_cons (by exact certified3939swap)
  apply certified_cons (by exact certified3940)
  apply certified_cons (by exact certified3940swap)
  apply certified_cons (by exact certified3941)
  apply certified_cons (by exact certified3941swap)
  apply certified_cons (by exact certified3942)
  apply certified_cons (by exact certified3942swap)
  apply certified_cons (by exact certified3943)
  apply certified_cons (by exact certified3943swap)
  apply certified_cons (by exact certified3944)
  apply certified_cons (by exact certified3944swap)
  apply certified_cons (by exact certified3945)
  apply certified_cons (by exact certified3945swap)
  apply certified_cons (by exact certified3946)
  apply certified_cons (by exact certified3946swap)
  apply certified_cons (by exact certified3947)
  apply certified_cons (by exact certified3947swap)
  apply certified_cons (by exact certified3948)
  apply certified_cons (by exact certified3948swap)
  apply certified_cons (by exact certified3949)
  apply certified_cons (by exact certified3949swap)
  simp
#print axioms certified_keys078
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
