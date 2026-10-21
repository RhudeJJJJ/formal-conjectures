/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core107 : Family 7 := level7.get ⟨114,by decide⟩
def sourceMap107 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,5,6,7,8,9,10,11,1,2,3,4] (sourceLabel 7 1 1 v)
def fusedMap107 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap107_checked : acceptsGraphIso
    (source (graph core107) (root 7) 1 1) SmallGeFourSpectrum232.graph
      sourceMap107=true := by decide +kernel
theorem fusedMap107_checked : acceptsGraphIso
    (fused (graph core107) (root 7) 1 1) SmallGeFourSpectrum112.graph
      fusedMap107=true := by decide +kernel
theorem certified107 : Certified (graph core107) (root 7) 1 1 :=
  of_native_maps core107 SmallGeFourSpectrum232.graph SmallGeFourSpectrum112.graph
    sourceMap107 fusedMap107 sourceMap107_checked fusedMap107_checked
    SmallGeFourComparisons.comparison107
#print axioms sourceMap107_checked
#print axioms fusedMap107_checked
#print axioms certified107
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
