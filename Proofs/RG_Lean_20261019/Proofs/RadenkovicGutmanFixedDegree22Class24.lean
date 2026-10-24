/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree22Class24Batch000
import Proofs.RadenkovicGutmanFixedDegree22Class24Batch001
import Proofs.RadenkovicGutmanFixedDegree22Class24Batch002

namespace Gebendorfer.RadenkovicGutman.FixedDegree22Class24
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree22Class24Cell000.slice,FixedDegree22Class24Cell001.slice,FixedDegree22Class24Cell002.slice,FixedDegree22Class24Cell003.slice,FixedDegree22Class24Cell004.slice,FixedDegree22Class24Cell005.slice,FixedDegree22Class24Cell006.slice,FixedDegree22Class24Cell007.slice,FixedDegree22Class24Cell008.slice,FixedDegree22Class24Cell009.slice,FixedDegree22Class24Cell010.slice,FixedDegree22Class24Cell011.slice,FixedDegree22Class24Cell012.slice,FixedDegree22Class24Cell013.slice,FixedDegree22Class24Cell014.slice,FixedDegree22Class24Cell015.slice,FixedDegree22Class24Cell016.slice,FixedDegree22Class24Cell017.slice,FixedDegree22Class24Cell018.slice,FixedDegree22Class24Cell019.slice,FixedDegree22Class24Cell020.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 22 1 3 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree22Class24Cell000.slice_checked,FixedDegree22Class24Cell001.slice_checked,FixedDegree22Class24Cell002.slice_checked,FixedDegree22Class24Cell003.slice_checked,FixedDegree22Class24Cell004.slice_checked,FixedDegree22Class24Cell005.slice_checked,FixedDegree22Class24Cell006.slice_checked,FixedDegree22Class24Cell007.slice_checked,FixedDegree22Class24Cell008.slice_checked,FixedDegree22Class24Cell009.slice_checked,FixedDegree22Class24Cell010.slice_checked,FixedDegree22Class24Cell011.slice_checked,FixedDegree22Class24Cell012.slice_checked,FixedDegree22Class24Cell013.slice_checked,FixedDegree22Class24Cell014.slice_checked,FixedDegree22Class24Cell015.slice_checked,FixedDegree22Class24Cell016.slice_checked,FixedDegree22Class24Cell017.slice_checked,FixedDegree22Class24Cell018.slice_checked,FixedDegree22Class24Cell019.slice_checked,FixedDegree22Class24Cell020.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 22 1 3 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 22 1 3 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=22)
    (hp : ArmClasses.classify p=1) (hq : ArmClasses.classify q=3) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 22 (by decide) hd 1 3 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree22Class24
