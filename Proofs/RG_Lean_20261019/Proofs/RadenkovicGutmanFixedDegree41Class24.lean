/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree41Class24Batch000
import Proofs.RadenkovicGutmanFixedDegree41Class24Batch001
import Proofs.RadenkovicGutmanFixedDegree41Class24Batch002

namespace Gebendorfer.RadenkovicGutman.FixedDegree41Class24
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree41Class24Cell000.slice,FixedDegree41Class24Cell001.slice,FixedDegree41Class24Cell002.slice,FixedDegree41Class24Cell003.slice,FixedDegree41Class24Cell004.slice,FixedDegree41Class24Cell005.slice,FixedDegree41Class24Cell006.slice,FixedDegree41Class24Cell007.slice,FixedDegree41Class24Cell008.slice,FixedDegree41Class24Cell009.slice,FixedDegree41Class24Cell010.slice,FixedDegree41Class24Cell011.slice,FixedDegree41Class24Cell012.slice,FixedDegree41Class24Cell013.slice,FixedDegree41Class24Cell014.slice,FixedDegree41Class24Cell015.slice,FixedDegree41Class24Cell016.slice,FixedDegree41Class24Cell017.slice,FixedDegree41Class24Cell018.slice,FixedDegree41Class24Cell019.slice,FixedDegree41Class24Cell020.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 41 1 3 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree41Class24Cell000.slice_checked,FixedDegree41Class24Cell001.slice_checked,FixedDegree41Class24Cell002.slice_checked,FixedDegree41Class24Cell003.slice_checked,FixedDegree41Class24Cell004.slice_checked,FixedDegree41Class24Cell005.slice_checked,FixedDegree41Class24Cell006.slice_checked,FixedDegree41Class24Cell007.slice_checked,FixedDegree41Class24Cell008.slice_checked,FixedDegree41Class24Cell009.slice_checked,FixedDegree41Class24Cell010.slice_checked,FixedDegree41Class24Cell011.slice_checked,FixedDegree41Class24Cell012.slice_checked,FixedDegree41Class24Cell013.slice_checked,FixedDegree41Class24Cell014.slice_checked,FixedDegree41Class24Cell015.slice_checked,FixedDegree41Class24Cell016.slice_checked,FixedDegree41Class24Cell017.slice_checked,FixedDegree41Class24Cell018.slice_checked,FixedDegree41Class24Cell019.slice_checked,FixedDegree41Class24Cell020.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 41 1 3 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 41 1 3 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=41)
    (hp : ArmClasses.classify p=1) (hq : ArmClasses.classify q=3) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 41 (by decide) hd 1 3 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree41Class24
