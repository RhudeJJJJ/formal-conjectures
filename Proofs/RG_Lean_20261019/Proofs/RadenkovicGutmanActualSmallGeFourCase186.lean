/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core186 : Family 9 := level9.get ⟨485,by decide⟩
def sourceMap186 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap186 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap186_checked : acceptsGraphIso
    (source (graph core186) (root 9) 0 0) SmallGeFourSpectrum115.graph
      sourceMap186=true := by decide +kernel
theorem fusedMap186_checked : acceptsGraphIso
    (fused (graph core186) (root 9) 0 0) SmallGeFourSpectrum182.graph
      fusedMap186=true := by decide +kernel
theorem certified186 : Certified (graph core186) (root 9) 0 0 :=
  of_native_maps core186 SmallGeFourSpectrum115.graph SmallGeFourSpectrum182.graph
    sourceMap186 fusedMap186 sourceMap186_checked fusedMap186_checked
    SmallGeFourComparisons.comparison186
#print axioms sourceMap186_checked
#print axioms fusedMap186_checked
#print axioms certified186
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
