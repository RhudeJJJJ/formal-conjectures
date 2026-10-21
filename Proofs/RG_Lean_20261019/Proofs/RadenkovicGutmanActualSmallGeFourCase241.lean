/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons14
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core241 : Family 9 := level9.get ⟨713,by decide⟩
def sourceMap241 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap241 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,6,7,8,9,10,11,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap241_checked : acceptsGraphIso
    (source (graph core241) (root 9) 0 0) SmallGeFourSpectrum198.graph
      sourceMap241=true := by decide +kernel
theorem fusedMap241_checked : acceptsGraphIso
    (fused (graph core241) (root 9) 0 0) SmallGeFourSpectrum228.graph
      fusedMap241=true := by decide +kernel
theorem certified241 : Certified (graph core241) (root 9) 0 0 :=
  of_native_maps core241 SmallGeFourSpectrum198.graph SmallGeFourSpectrum228.graph
    sourceMap241 fusedMap241 sourceMap241_checked fusedMap241_checked
    SmallGeFourComparisons.comparison241
#print axioms sourceMap241_checked
#print axioms fusedMap241_checked
#print axioms certified241
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
