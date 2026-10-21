/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core201 : Family 9 := level9.get ⟨607,by decide⟩
def sourceMap201 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap201 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap201_checked : acceptsGraphIso
    (source (graph core201) (root 9) 0 0) SmallGeFourSpectrum212.graph
      sourceMap201=true := by decide +kernel
theorem fusedMap201_checked : acceptsGraphIso
    (fused (graph core201) (root 9) 0 0) SmallGeFourSpectrum150.graph
      fusedMap201=true := by decide +kernel
theorem certified201 : Certified (graph core201) (root 9) 0 0 :=
  of_native_maps core201 SmallGeFourSpectrum212.graph SmallGeFourSpectrum150.graph
    sourceMap201 fusedMap201 sourceMap201_checked fusedMap201_checked
    SmallGeFourComparisons.comparison201
#print axioms sourceMap201_checked
#print axioms fusedMap201_checked
#print axioms certified201
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
