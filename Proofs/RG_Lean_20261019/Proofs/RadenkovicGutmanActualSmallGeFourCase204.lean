/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core204 : Family 9 := level9.get ⟨621,by decide⟩
def sourceMap204 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap204 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap204_checked : acceptsGraphIso
    (source (graph core204) (root 9) 0 0) SmallGeFourSpectrum162.graph
      sourceMap204=true := by decide +kernel
theorem fusedMap204_checked : acceptsGraphIso
    (fused (graph core204) (root 9) 0 0) SmallGeFourSpectrum161.graph
      fusedMap204=true := by decide +kernel
theorem certified204 : Certified (graph core204) (root 9) 0 0 :=
  of_native_maps core204 SmallGeFourSpectrum162.graph SmallGeFourSpectrum161.graph
    sourceMap204 fusedMap204 sourceMap204_checked fusedMap204_checked
    SmallGeFourComparisons.comparison204
#print axioms sourceMap204_checked
#print axioms fusedMap204_checked
#print axioms certified204
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
