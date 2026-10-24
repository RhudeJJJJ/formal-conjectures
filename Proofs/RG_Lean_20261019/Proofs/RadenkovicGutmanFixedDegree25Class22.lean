/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree25Class22Batch000
import Proofs.RadenkovicGutmanFixedDegree25Class22Batch001

namespace Gebendorfer.RadenkovicGutman.FixedDegree25Class22
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree25Class22Cell000.slice,FixedDegree25Class22Cell001.slice,FixedDegree25Class22Cell002.slice,FixedDegree25Class22Cell003.slice,FixedDegree25Class22Cell004.slice,FixedDegree25Class22Cell005.slice,FixedDegree25Class22Cell006.slice,FixedDegree25Class22Cell007.slice,FixedDegree25Class22Cell008.slice,FixedDegree25Class22Cell009.slice,FixedDegree25Class22Cell010.slice,FixedDegree25Class22Cell011.slice,FixedDegree25Class22Cell012.slice,FixedDegree25Class22Cell013.slice,FixedDegree25Class22Cell014.slice,FixedDegree25Class22Cell015.slice,FixedDegree25Class22Cell016.slice,FixedDegree25Class22Cell017.slice,FixedDegree25Class22Cell018.slice,FixedDegree25Class22Cell019.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 25 1 1 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree25Class22Cell000.slice_checked,FixedDegree25Class22Cell001.slice_checked,FixedDegree25Class22Cell002.slice_checked,FixedDegree25Class22Cell003.slice_checked,FixedDegree25Class22Cell004.slice_checked,FixedDegree25Class22Cell005.slice_checked,FixedDegree25Class22Cell006.slice_checked,FixedDegree25Class22Cell007.slice_checked,FixedDegree25Class22Cell008.slice_checked,FixedDegree25Class22Cell009.slice_checked,FixedDegree25Class22Cell010.slice_checked,FixedDegree25Class22Cell011.slice_checked,FixedDegree25Class22Cell012.slice_checked,FixedDegree25Class22Cell013.slice_checked,FixedDegree25Class22Cell014.slice_checked,FixedDegree25Class22Cell015.slice_checked,FixedDegree25Class22Cell016.slice_checked,FixedDegree25Class22Cell017.slice_checked,FixedDegree25Class22Cell018.slice_checked,FixedDegree25Class22Cell019.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 25 1 1 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 25 1 1 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=25)
    (hp : ArmClasses.classify p=1) (hq : ArmClasses.classify q=1) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 25 (by decide) hd 1 1 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree25Class22
