/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core105 : Family 7 := level7.get ⟨114,by decide⟩
def sourceMap105 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 7 0 1 v)
def fusedMap105 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap105_checked : acceptsGraphIso
    (source (graph core105) (root 7) 0 1) SmallGeFourSpectrum069.graph
      sourceMap105=true := by decide +kernel
theorem fusedMap105_checked : acceptsGraphIso
    (fused (graph core105) (root 7) 0 1) SmallGeFourSpectrum071.graph
      fusedMap105=true := by decide +kernel
theorem certified105 : Certified (graph core105) (root 7) 0 1 :=
  of_native_maps core105 SmallGeFourSpectrum069.graph SmallGeFourSpectrum071.graph
    sourceMap105 fusedMap105 sourceMap105_checked fusedMap105_checked
    SmallGeFourComparisons.comparison105
#print axioms sourceMap105_checked
#print axioms fusedMap105_checked
#print axioms certified105
def sourceMap105swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,8] (sourceLabel 7 1 0 v)
def fusedMap105swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap105swap_checked : acceptsGraphIso
    (source (graph core105) (root 7) 1 0) SmallGeFourSpectrum069.graph
      sourceMap105swap=true := by decide +kernel
theorem fusedMap105swap_checked : acceptsGraphIso
    (fused (graph core105) (root 7) 1 0) SmallGeFourSpectrum071.graph
      fusedMap105swap=true := by decide +kernel
theorem certified105swap : Certified (graph core105) (root 7) 1 0 :=
  of_native_maps core105 SmallGeFourSpectrum069.graph SmallGeFourSpectrum071.graph
    sourceMap105swap fusedMap105swap sourceMap105swap_checked fusedMap105swap_checked
    SmallGeFourComparisons.comparison105
#print axioms sourceMap105swap_checked
#print axioms fusedMap105swap_checked
#print axioms certified105swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
