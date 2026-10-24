/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree02Class40Batch000
import Proofs.RadenkovicGutmanFixedDegree02Class40Batch001
import Proofs.RadenkovicGutmanFixedDegree02Class40Batch002

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class40
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree02Class40Cell000.slice,FixedDegree02Class40Cell001.slice,FixedDegree02Class40Cell002.slice,FixedDegree02Class40Cell003.slice,FixedDegree02Class40Cell004.slice,FixedDegree02Class40Cell005.slice,FixedDegree02Class40Cell006.slice,FixedDegree02Class40Cell007.slice,FixedDegree02Class40Cell008.slice,FixedDegree02Class40Cell009.slice,FixedDegree02Class40Cell010.slice,FixedDegree02Class40Cell011.slice,FixedDegree02Class40Cell012.slice,FixedDegree02Class40Cell013.slice,FixedDegree02Class40Cell014.slice,FixedDegree02Class40Cell015.slice,FixedDegree02Class40Cell016.slice,FixedDegree02Class40Cell017.slice,FixedDegree02Class40Cell018.slice,FixedDegree02Class40Cell019.slice,FixedDegree02Class40Cell020.slice,FixedDegree02Class40Cell021.slice,FixedDegree02Class40Cell022.slice]
def reserve : ℚ := (2/17)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 2 3 4 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree02Class40Cell000.slice_checked,FixedDegree02Class40Cell001.slice_checked,FixedDegree02Class40Cell002.slice_checked,FixedDegree02Class40Cell003.slice_checked,FixedDegree02Class40Cell004.slice_checked,FixedDegree02Class40Cell005.slice_checked,FixedDegree02Class40Cell006.slice_checked,FixedDegree02Class40Cell007.slice_checked,FixedDegree02Class40Cell008.slice_checked,FixedDegree02Class40Cell009.slice_checked,FixedDegree02Class40Cell010.slice_checked,FixedDegree02Class40Cell011.slice_checked,FixedDegree02Class40Cell012.slice_checked,FixedDegree02Class40Cell013.slice_checked,FixedDegree02Class40Cell014.slice_checked,FixedDegree02Class40Cell015.slice_checked,FixedDegree02Class40Cell016.slice_checked,FixedDegree02Class40Cell017.slice_checked,FixedDegree02Class40Cell018.slice_checked,FixedDegree02Class40Cell019.slice_checked,FixedDegree02Class40Cell020.slice_checked,FixedDegree02Class40Cell021.slice_checked,FixedDegree02Class40Cell022.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 2 3 4 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 2 3 4 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=2)
    (hp : ArmClasses.classify p=3) (hq : ArmClasses.classify q=4) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 2 (by decide) hd 3 4 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree02Class40
