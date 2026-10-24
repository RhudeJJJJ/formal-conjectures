/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedClassKernelBase
import Proofs.RadenkovicGutmanFixedDegree10Class33Batch000
import Proofs.RadenkovicGutmanFixedDegree10Class33Batch001
import Proofs.RadenkovicGutmanFixedDegree10Class33Batch002
import Proofs.RadenkovicGutmanFixedDegree10Class33Batch003

namespace Gebendorfer.RadenkovicGutman.FixedDegree10Class33
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def partition : List FastArmCoverIntegral.Slice := [FixedDegree10Class33Cell000.slice,FixedDegree10Class33Cell001.slice,FixedDegree10Class33Cell002.slice,FixedDegree10Class33Cell003.slice,FixedDegree10Class33Cell004.slice,FixedDegree10Class33Cell005.slice,FixedDegree10Class33Cell006.slice,FixedDegree10Class33Cell007.slice,FixedDegree10Class33Cell008.slice,FixedDegree10Class33Cell009.slice,FixedDegree10Class33Cell010.slice,FixedDegree10Class33Cell011.slice,FixedDegree10Class33Cell012.slice,FixedDegree10Class33Cell013.slice,FixedDegree10Class33Cell014.slice,FixedDegree10Class33Cell015.slice,FixedDegree10Class33Cell016.slice,FixedDegree10Class33Cell017.slice,FixedDegree10Class33Cell018.slice,FixedDegree10Class33Cell019.slice,FixedDegree10Class33Cell020.slice,FixedDegree10Class33Cell021.slice,FixedDegree10Class33Cell022.slice,FixedDegree10Class33Cell023.slice,FixedDegree10Class33Cell024.slice,FixedDegree10Class33Cell025.slice,FixedDegree10Class33Cell026.slice,FixedDegree10Class33Cell027.slice,FixedDegree10Class33Cell028.slice,FixedDegree10Class33Cell029.slice,FixedDegree10Class33Cell030.slice,FixedDegree10Class33Cell031.slice,FixedDegree10Class33Cell032.slice,FixedDegree10Class33Cell033.slice,FixedDegree10Class33Cell034.slice,FixedDegree10Class33Cell035.slice,FixedDegree10Class33Cell036.slice,FixedDegree10Class33Cell037.slice]
def reserve : ℚ := (2/13)
theorem all_checked : ∀ s∈partition, FastArmCoverIntegral.accepts 10 2 2 s=true := by
  simp only [partition,List.forall_mem_cons]
  exact ⟨FixedDegree10Class33Cell000.slice_checked,FixedDegree10Class33Cell001.slice_checked,FixedDegree10Class33Cell002.slice_checked,FixedDegree10Class33Cell003.slice_checked,FixedDegree10Class33Cell004.slice_checked,FixedDegree10Class33Cell005.slice_checked,FixedDegree10Class33Cell006.slice_checked,FixedDegree10Class33Cell007.slice_checked,FixedDegree10Class33Cell008.slice_checked,FixedDegree10Class33Cell009.slice_checked,FixedDegree10Class33Cell010.slice_checked,FixedDegree10Class33Cell011.slice_checked,FixedDegree10Class33Cell012.slice_checked,FixedDegree10Class33Cell013.slice_checked,FixedDegree10Class33Cell014.slice_checked,FixedDegree10Class33Cell015.slice_checked,FixedDegree10Class33Cell016.slice_checked,FixedDegree10Class33Cell017.slice_checked,FixedDegree10Class33Cell018.slice_checked,FixedDegree10Class33Cell019.slice_checked,FixedDegree10Class33Cell020.slice_checked,FixedDegree10Class33Cell021.slice_checked,FixedDegree10Class33Cell022.slice_checked,FixedDegree10Class33Cell023.slice_checked,FixedDegree10Class33Cell024.slice_checked,FixedDegree10Class33Cell025.slice_checked,FixedDegree10Class33Cell026.slice_checked,FixedDegree10Class33Cell027.slice_checked,FixedDegree10Class33Cell028.slice_checked,FixedDegree10Class33Cell029.slice_checked,FixedDegree10Class33Cell030.slice_checked,FixedDegree10Class33Cell031.slice_checked,FixedDegree10Class33Cell032.slice_checked,FixedDegree10Class33Cell033.slice_checked,FixedDegree10Class33Cell034.slice_checked,FixedDegree10Class33Cell035.slice_checked,FixedDegree10Class33Cell036.slice_checked,FixedDegree10Class33Cell037.slice_checked,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem adjacent_checked : FixedClassChain.adjacent (1/1000) 1024 partition=true := by decide +kernel
theorem partition_checked : FastArmCoverIntegral.checkAt 10 2 2 (1/1000) 1024 partition=true :=
  FixedClassChain.check_of_adjacent 10 2 2 (1/1000) 1024 partition adjacent_checked all_checked
theorem budget_checked : PaidFixedClassIntegral.accepts reserve (FastArmCoverIntegral.payment partition)=true := by decide +kernel
open scoped Classical
noncomputable section
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (p q : ℕ) (hd : G.degree u=10)
    (hp : ArmClasses.classify p=2) (hq : ArmClasses.classify q=2) :
    (reserve : ℝ)<ActualFusionIntegral.normalizedIntegral G u p q 2 :=
  PaidFixedClassIntegral.normalized_target G u p q 10 (by decide) hd 2 2 hp hq
    reserve partition partition_checked budget_checked
end
#print axioms all_checked
#print axioms adjacent_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end Gebendorfer.RadenkovicGutman.FixedDegree10Class33
