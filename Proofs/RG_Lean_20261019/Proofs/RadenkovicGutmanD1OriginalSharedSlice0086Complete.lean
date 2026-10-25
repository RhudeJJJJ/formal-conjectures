/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01462
import Proofs.RadenkovicGutmanD1Long00Leaf01463
import Proofs.RadenkovicGutmanD1Long00Leaf01464
import Proofs.RadenkovicGutmanD1Long00Leaf01465
import Proofs.RadenkovicGutmanD1Long00Leaf01466
import Proofs.RadenkovicGutmanD1Long00Leaf01467
import Proofs.RadenkovicGutmanD1Long00Leaf01468
import Proofs.RadenkovicGutmanD1Long00Leaf01469
import Proofs.RadenkovicGutmanD1Long00Leaf01470
import Proofs.RadenkovicGutmanD1Long00Leaf01471
import Proofs.RadenkovicGutmanD1Long00Leaf01472
import Proofs.RadenkovicGutmanD1Long00Leaf01473
import Proofs.RadenkovicGutmanD1Long00Leaf01474
import Proofs.RadenkovicGutmanD1Long00Leaf01475
import Proofs.RadenkovicGutmanD1Long00Leaf01476
import Proofs.RadenkovicGutmanD1Long00Leaf01477
import Proofs.RadenkovicGutmanD1Long00Leaf01478
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0086Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01462) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01463) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01464) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01465) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01466) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01467) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01468) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01469) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01470) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01471) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01472) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01473) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01474) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01475) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01476) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01477) (.leaf DegreeOneLongClass00.leaf01478))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(64/15),(32/7),(150124047/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (64/15) (32/7) 0 1 0 1 (150124047/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01462_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01463_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01464_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01465_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01466_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01467_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01468_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01469_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01470_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01471_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01472_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01473_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01474_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01475_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01476_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01477_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01478_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((32/7) : ℚ) : ℝ)-(((64/15) : ℚ) : ℝ))*(((150124047/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((64/15) : ℚ) : ℝ)..(((32/7) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0086Complete
