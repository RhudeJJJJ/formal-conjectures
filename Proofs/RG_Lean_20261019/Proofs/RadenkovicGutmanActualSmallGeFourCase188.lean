/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core188 : Family 9 := level9.get ⟨516,by decide⟩
def sourceMap188 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,7,8,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap188 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap188_checked : acceptsGraphIso
    (source (graph core188) (root 9) 0 0) SmallGeFourSpectrum118.graph
      sourceMap188=true := by decide +kernel
theorem fusedMap188_checked : acceptsGraphIso
    (fused (graph core188) (root 9) 0 0) SmallGeFourSpectrum188.graph
      fusedMap188=true := by decide +kernel
theorem certified188 : Certified (graph core188) (root 9) 0 0 :=
  of_native_maps core188 SmallGeFourSpectrum118.graph SmallGeFourSpectrum188.graph
    sourceMap188 fusedMap188 sourceMap188_checked fusedMap188_checked
    SmallGeFourComparisons.comparison188
#print axioms sourceMap188_checked
#print axioms fusedMap188_checked
#print axioms certified188
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
