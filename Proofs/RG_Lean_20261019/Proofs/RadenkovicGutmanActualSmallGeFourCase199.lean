/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core199 : Family 9 := level9.get ⟨584,by decide⟩
def sourceMap199 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap199 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap199_checked : acceptsGraphIso
    (source (graph core199) (root 9) 0 0) SmallGeFourSpectrum204.graph
      sourceMap199=true := by decide +kernel
theorem fusedMap199_checked : acceptsGraphIso
    (fused (graph core199) (root 9) 0 0) SmallGeFourSpectrum136.graph
      fusedMap199=true := by decide +kernel
theorem certified199 : Certified (graph core199) (root 9) 0 0 :=
  of_native_maps core199 SmallGeFourSpectrum204.graph SmallGeFourSpectrum136.graph
    sourceMap199 fusedMap199 sourceMap199_checked fusedMap199_checked
    SmallGeFourComparisons.comparison199
#print axioms sourceMap199_checked
#print axioms fusedMap199_checked
#print axioms certified199
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
