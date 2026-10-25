/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanOriginalAssembly
import Proofs.RadenkovicGutmanDegreeOneClassDispatch
import Proofs.RadenkovicGutmanFirstClassNormalized
import Proofs.RadenkovicGutmanD1Short12
import Proofs.RadenkovicGutmanD1Short13
import Proofs.RadenkovicGutmanD1Short14
import Proofs.RadenkovicGutmanD1Short22
import Proofs.RadenkovicGutmanD1Short23
import Proofs.RadenkovicGutmanD1Short24
import Proofs.RadenkovicGutmanD1Short33
import Proofs.RadenkovicGutmanD1Short34
import Proofs.RadenkovicGutmanD1Short44
import Proofs.RadenkovicGutmanD1Long10
import Proofs.RadenkovicGutmanD1Long20
import Proofs.RadenkovicGutmanD1Long30
import Proofs.RadenkovicGutmanD1Long40
import Proofs.RadenkovicGutmanD1OriginalSharedBothLong

/-! The concrete fifteen-class assembly. Its complete kernel check still requires
all original long-long leaf proofs and the new shared-tree class endpoint. -/
namespace Gebendorfer.RadenkovicGutman.OriginalDegreeOneLarge
open SimpleGraph CoreQuotient ActualFusionIntegral OriginalAssembly
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

theorem certificates : DegreeOneClassDispatch.Certificates where
  class00 := by
    intro m C u p q hd hp hq
    have hp0 : p=0 := by
      have h := congrArg Fin.val hp
      change min p 4=0 at h
      omega
    have hq0 : q=0 := by
      have h := congrArg Fin.val hq
      change min q 4=0 at h
      omega
    subst p
    subst q
    exact FirstClassNormalized.normalized_target C u hd
  class01 := fun _ C u p q hd hp hq => DegreeOneShortClass12.normalized_target C u p q hd hp hq
  class02 := fun _ C u p q hd hp hq => DegreeOneShortClass13.normalized_target C u p q hd hp hq
  class03 := fun _ C u p q hd hp hq => DegreeOneShortClass14.normalized_target C u p q hd hp hq
  class04 := fun _ C u p q hd hp hq => DegreeOneLongClass10.normalized_target C u p q hd hp hq
  class11 := fun _ C u p q hd hp hq => DegreeOneShortClass22.normalized_target C u p q hd hp hq
  class12 := fun _ C u p q hd hp hq => DegreeOneShortClass23.normalized_target C u p q hd hp hq
  class13 := fun _ C u p q hd hp hq => DegreeOneShortClass24.normalized_target C u p q hd hp hq
  class14 := fun _ C u p q hd hp hq => DegreeOneLongClass20.normalized_target C u p q hd hp hq
  class22 := fun _ C u p q hd hp hq => DegreeOneShortClass33.normalized_target C u p q hd hp hq
  class23 := fun _ C u p q hd hp hq => DegreeOneShortClass34.normalized_target C u p q hd hp hq
  class24 := fun _ C u p q hd hp hq => DegreeOneLongClass30.normalized_target C u p q hd hp hq
  class33 := fun _ C u p q hd hp hq => DegreeOneShortClass44.normalized_target C u p q hd hp hq
  class34 := fun _ C u p q hd hp hq => DegreeOneLongClass40.normalized_target C u p q hd hp hq
  class44 := by
    intro m C u p q hd hp hq
    simpa only [D1OriginalSharedBothLong.reserve,Rat.cast_div,Rat.cast_ofNat] using
      D1OriginalSharedBothLong.normalized_target C u p q hd hp hq

theorem input_family (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (_hT : (source C u p q).IsTree) (hd : C.degree u=1) (_hN : 53≤order C p q) :
    (189/5000 : ℝ)<normalizedIntegral C u p q 2 :=
  DegreeOneClassDispatch.normalized_target certificates m C u p q hd

#print axioms certificates
#print axioms input_family
end
end Gebendorfer.RadenkovicGutman.OriginalDegreeOneLarge
