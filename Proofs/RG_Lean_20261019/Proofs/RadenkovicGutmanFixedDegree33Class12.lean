/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree33Class12Batch000
import Proofs.RadenkovicGutmanFixedDegree33Class12Batch001

namespace Gebendorfer.RadenkovicGutman.FixedDegree33Class12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree33Class12Cell000.slice,FixedDegree33Class12Cell001.slice,FixedDegree33Class12Cell002.slice,FixedDegree33Class12Cell003.slice,FixedDegree33Class12Cell004.slice,FixedDegree33Class12Cell005.slice,FixedDegree33Class12Cell006.slice,FixedDegree33Class12Cell007.slice,FixedDegree33Class12Cell008.slice,FixedDegree33Class12Cell009.slice,FixedDegree33Class12Cell010.slice,FixedDegree33Class12Cell011.slice,FixedDegree33Class12Cell012.slice,FixedDegree33Class12Cell013.slice,FixedDegree33Class12Cell014.slice,FixedDegree33Class12Cell015.slice,FixedDegree33Class12Cell016.slice,FixedDegree33Class12Cell017.slice,FixedDegree33Class12Cell018.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 33 0 1 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree33Class12Cell000.slice_checked,FixedDegree33Class12Cell001.slice_checked,FixedDegree33Class12Cell002.slice_checked,FixedDegree33Class12Cell003.slice_checked,FixedDegree33Class12Cell004.slice_checked,FixedDegree33Class12Cell005.slice_checked,FixedDegree33Class12Cell006.slice_checked,FixedDegree33Class12Cell007.slice_checked,FixedDegree33Class12Cell008.slice_checked,FixedDegree33Class12Cell009.slice_checked,FixedDegree33Class12Cell010.slice_checked,FixedDegree33Class12Cell011.slice_checked,FixedDegree33Class12Cell012.slice_checked,FixedDegree33Class12Cell013.slice_checked,FixedDegree33Class12Cell014.slice_checked,FixedDegree33Class12Cell015.slice_checked,FixedDegree33Class12Cell016.slice_checked,FixedDegree33Class12Cell017.slice_checked,FixedDegree33Class12Cell018.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 33 0 1 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 33 0 1 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=33)
    (hp : ArmClasses.classify p=0) (hq : ArmClasses.classify q=1) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 33 (by decide) hd 0 1 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree33Class12
