/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons14
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core240 : Family 9 := level9.get ⟨712,by decide⟩
def sourceMap240 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap240 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap240_checked : acceptsGraphIso
    (source (graph core240) (root 9) 0 0) SmallGeFourSpectrum228.graph
      sourceMap240=true := by decide +kernel
theorem fusedMap240_checked : acceptsGraphIso
    (fused (graph core240) (root 9) 0 0) SmallGeFourSpectrum227.graph
      fusedMap240=true := by decide +kernel
theorem certified240 : Certified (graph core240) (root 9) 0 0 :=
  of_native_maps core240 SmallGeFourSpectrum228.graph SmallGeFourSpectrum227.graph
    sourceMap240 fusedMap240 sourceMap240_checked fusedMap240_checked
    SmallGeFourComparisons.comparison240
#print axioms sourceMap240_checked
#print axioms fusedMap240_checked
#print axioms certified240
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
