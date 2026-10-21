/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core152 : Family 8 := level8.get ⟨277,by decide⟩
def sourceMap152 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap152 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap152_checked : acceptsGraphIso
    (source (graph core152) (root 8) 0 0) SmallGeFourSpectrum084.graph
      sourceMap152=true := by decide +kernel
theorem fusedMap152_checked : acceptsGraphIso
    (fused (graph core152) (root 8) 0 0) SmallGeFourSpectrum083.graph
      fusedMap152=true := by decide +kernel
theorem certified152 : Certified (graph core152) (root 8) 0 0 :=
  of_native_maps core152 SmallGeFourSpectrum084.graph SmallGeFourSpectrum083.graph
    sourceMap152 fusedMap152 sourceMap152_checked fusedMap152_checked
    SmallGeFourComparisons.comparison152
#print axioms sourceMap152_checked
#print axioms fusedMap152_checked
#print axioms certified152
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
