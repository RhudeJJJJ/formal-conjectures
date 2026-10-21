/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core206 : Family 9 := level9.get ⟨626,by decide⟩
def sourceMap206 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![4,0,1,2,3,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap206 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![4,0,1,2,3,5,6,7,8,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap206_checked : acceptsGraphIso
    (source (graph core206) (root 9) 0 0) SmallGeFourSpectrum156.graph
      sourceMap206=true := by decide +kernel
theorem fusedMap206_checked : acceptsGraphIso
    (fused (graph core206) (root 9) 0 0) SmallGeFourSpectrum155.graph
      fusedMap206=true := by decide +kernel
theorem certified206 : Certified (graph core206) (root 9) 0 0 :=
  of_native_maps core206 SmallGeFourSpectrum156.graph SmallGeFourSpectrum155.graph
    sourceMap206 fusedMap206 sourceMap206_checked fusedMap206_checked
    SmallGeFourComparisons.comparison206
#print axioms sourceMap206_checked
#print axioms fusedMap206_checked
#print axioms certified206
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
