/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00357
import Proofs.RadenkovicGutmanD1Long00Leaf00358
import Proofs.RadenkovicGutmanD1Long00Leaf00359
import Proofs.RadenkovicGutmanD1Long00Leaf00360
import Proofs.RadenkovicGutmanD1Long00Leaf00361
import Proofs.RadenkovicGutmanD1Long00Leaf00362
import Proofs.RadenkovicGutmanD1Long00Leaf00363
import Proofs.RadenkovicGutmanD1Long00Leaf00364
import Proofs.RadenkovicGutmanD1Long00Leaf00365
import Proofs.RadenkovicGutmanD1Long00Leaf00366
import Proofs.RadenkovicGutmanD1Long00Leaf00367
import Proofs.RadenkovicGutmanD1Long00Leaf00368
import Proofs.RadenkovicGutmanD1Long00Leaf00369
import Proofs.RadenkovicGutmanD1Long00Leaf00370
import Proofs.RadenkovicGutmanD1Long00Leaf00371
import Proofs.RadenkovicGutmanD1Long00Leaf00372
import Proofs.RadenkovicGutmanD1Long00Leaf00373
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0021Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00357) (.leaf DegreeOneLongClass00.leaf00358)) (.leaf DegreeOneLongClass00.leaf00359)) (.leaf DegreeOneLongClass00.leaf00360)) (.leaf DegreeOneLongClass00.leaf00361)) (.leaf DegreeOneLongClass00.leaf00362)) (.leaf DegreeOneLongClass00.leaf00363)) (.leaf DegreeOneLongClass00.leaf00364)) (.leaf DegreeOneLongClass00.leaf00365)) (.leaf DegreeOneLongClass00.leaf00366)) (.leaf DegreeOneLongClass00.leaf00367)) (.leaf DegreeOneLongClass00.leaf00368)) (.leaf DegreeOneLongClass00.leaf00369)) (.leaf DegreeOneLongClass00.leaf00370)) (.leaf DegreeOneLongClass00.leaf00371)) (.leaf DegreeOneLongClass00.leaf00372)) (.leaf DegreeOneLongClass00.leaf00373)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(13/1600),(7/800),(-6881398891/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (13/1600) (7/800) 0 1 0 1 (-6881398891/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00357_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00358_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00359_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00360_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00361_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00362_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00363_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00364_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00365_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00366_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00367_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00368_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00369_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00370_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00371_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00372_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00373_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((7/800) : ℚ) : ℝ)-(((13/1600) : ℚ) : ℝ))*(((-6881398891/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((13/1600) : ℚ) : ℝ)..(((7/800) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0021Complete
