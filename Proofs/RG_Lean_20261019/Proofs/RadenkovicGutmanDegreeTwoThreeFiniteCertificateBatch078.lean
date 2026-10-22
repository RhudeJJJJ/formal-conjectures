/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3900
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3901
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3902
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3903
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3904
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3905
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3906
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3907
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3908
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3909
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3910
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3911
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3912
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3913
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3914
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3915
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3916
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3917
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3918
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3919
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3920
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3921
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3922
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3923
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3924
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3925
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3926
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3927
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3928
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3929
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3930
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3931
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3932
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3933
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3934
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3935
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3936
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3937
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3938
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3939
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3940
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3941
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3942
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3943
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3944
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3945
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3946
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3947
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3948
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3949
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
