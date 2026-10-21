/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core190 : Family 9 := level9.get ⟨525,by decide⟩
def sourceMap190 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,8,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap190 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap190_checked : acceptsGraphIso
    (source (graph core190) (root 9) 0 0) SmallGeFourSpectrum113.graph
      sourceMap190=true := by decide +kernel
theorem fusedMap190_checked : acceptsGraphIso
    (fused (graph core190) (root 9) 0 0) SmallGeFourSpectrum183.graph
      fusedMap190=true := by decide +kernel
theorem certified190 : Certified (graph core190) (root 9) 0 0 :=
  of_native_maps core190 SmallGeFourSpectrum113.graph SmallGeFourSpectrum183.graph
    sourceMap190 fusedMap190 sourceMap190_checked fusedMap190_checked
    SmallGeFourComparisons.comparison190
#print axioms sourceMap190_checked
#print axioms fusedMap190_checked
#print axioms certified190
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
