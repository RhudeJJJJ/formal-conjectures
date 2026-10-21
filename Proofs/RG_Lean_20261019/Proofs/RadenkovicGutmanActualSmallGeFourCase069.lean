/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core069 : Family 7 := level7.get ⟨93,by decide⟩
def sourceMap069 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,7,8,9,10,3,4,5,6,1,2] (sourceLabel 7 0 1 v)
def fusedMap069 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,8,9,10,5,6,7] (fusedLabel 7 0 1 v)
theorem sourceMap069_checked : acceptsGraphIso
    (source (graph core069) (root 7) 0 1) SmallGeFourSpectrum061.graph
      sourceMap069=true := by decide +kernel
theorem fusedMap069_checked : acceptsGraphIso
    (fused (graph core069) (root 7) 0 1) SmallGeFourSpectrum066.graph
      fusedMap069=true := by decide +kernel
theorem certified069 : Certified (graph core069) (root 7) 0 1 :=
  of_native_maps core069 SmallGeFourSpectrum061.graph SmallGeFourSpectrum066.graph
    sourceMap069 fusedMap069 sourceMap069_checked fusedMap069_checked
    SmallGeFourComparisons.comparison069
#print axioms sourceMap069_checked
#print axioms fusedMap069_checked
#print axioms certified069
def sourceMap069swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,7,8,9,10,3,4,5,1,2,6] (sourceLabel 7 1 0 v)
def fusedMap069swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,8,9,10,5,6,7] (fusedLabel 7 1 0 v)
theorem sourceMap069swap_checked : acceptsGraphIso
    (source (graph core069) (root 7) 1 0) SmallGeFourSpectrum061.graph
      sourceMap069swap=true := by decide +kernel
theorem fusedMap069swap_checked : acceptsGraphIso
    (fused (graph core069) (root 7) 1 0) SmallGeFourSpectrum066.graph
      fusedMap069swap=true := by decide +kernel
theorem certified069swap : Certified (graph core069) (root 7) 1 0 :=
  of_native_maps core069 SmallGeFourSpectrum061.graph SmallGeFourSpectrum066.graph
    sourceMap069swap fusedMap069swap sourceMap069swap_checked fusedMap069swap_checked
    SmallGeFourComparisons.comparison069
#print axioms sourceMap069swap_checked
#print axioms fusedMap069swap_checked
#print axioms certified069swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
