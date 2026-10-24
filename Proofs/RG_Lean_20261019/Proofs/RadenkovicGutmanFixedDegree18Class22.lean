/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree18Class22Batch000
import Proofs.RadenkovicGutmanFixedDegree18Class22Batch001
import Proofs.RadenkovicGutmanFixedDegree18Class22Batch002

namespace Gebendorfer.RadenkovicGutman.FixedDegree18Class22
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree18Class22Cell000.slice,FixedDegree18Class22Cell001.slice,FixedDegree18Class22Cell002.slice,FixedDegree18Class22Cell003.slice,FixedDegree18Class22Cell004.slice,FixedDegree18Class22Cell005.slice,FixedDegree18Class22Cell006.slice,FixedDegree18Class22Cell007.slice,FixedDegree18Class22Cell008.slice,FixedDegree18Class22Cell009.slice,FixedDegree18Class22Cell010.slice,FixedDegree18Class22Cell011.slice,FixedDegree18Class22Cell012.slice,FixedDegree18Class22Cell013.slice,FixedDegree18Class22Cell014.slice,FixedDegree18Class22Cell015.slice,FixedDegree18Class22Cell016.slice,FixedDegree18Class22Cell017.slice,FixedDegree18Class22Cell018.slice,FixedDegree18Class22Cell019.slice,FixedDegree18Class22Cell020.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 18 1 1 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree18Class22Cell000.slice_checked,FixedDegree18Class22Cell001.slice_checked,FixedDegree18Class22Cell002.slice_checked,FixedDegree18Class22Cell003.slice_checked,FixedDegree18Class22Cell004.slice_checked,FixedDegree18Class22Cell005.slice_checked,FixedDegree18Class22Cell006.slice_checked,FixedDegree18Class22Cell007.slice_checked,FixedDegree18Class22Cell008.slice_checked,FixedDegree18Class22Cell009.slice_checked,FixedDegree18Class22Cell010.slice_checked,FixedDegree18Class22Cell011.slice_checked,FixedDegree18Class22Cell012.slice_checked,FixedDegree18Class22Cell013.slice_checked,FixedDegree18Class22Cell014.slice_checked,FixedDegree18Class22Cell015.slice_checked,FixedDegree18Class22Cell016.slice_checked,FixedDegree18Class22Cell017.slice_checked,FixedDegree18Class22Cell018.slice_checked,FixedDegree18Class22Cell019.slice_checked,FixedDegree18Class22Cell020.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 18 1 1 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 18 1 1 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=18)
    (hp : ArmClasses.classify p=1) (hq : ArmClasses.classify q=1) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 18 (by decide) hd 1 1 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree18Class22
