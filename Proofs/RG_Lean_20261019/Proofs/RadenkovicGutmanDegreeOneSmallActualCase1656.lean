/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1656 : Family 9 := level9.get ⟨415,by decide⟩
def sourceMap1656 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1656 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1656_checked : acceptsGraphIso
    (source (graph core1656) (root 9) 0 1) DegreeOneSmallSpectrum1892.graph sourceMap1656=true := by decide +kernel
theorem fusedMap1656_checked : acceptsGraphIso
    (fused (graph core1656) (root 9) 0 1) DegreeOneSmallSpectrum1292.graph fusedMap1656=true := by decide +kernel
theorem certified1656 : Certified (graph core1656) (root 9) 0 1 :=
  of_native_maps core1656 DegreeOneSmallSpectrum1892.graph DegreeOneSmallSpectrum1292.graph
    sourceMap1656 fusedMap1656 sourceMap1656_checked fusedMap1656_checked
    DegreeOneSmallComparisons.comparison1656
#print axioms sourceMap1656_checked
#print axioms fusedMap1656_checked
#print axioms certified1656
def sourceMap1656swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1656swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1656swap_checked : acceptsGraphIso
    (source (graph core1656) (root 9) 1 0) DegreeOneSmallSpectrum1892.graph sourceMap1656swap=true := by decide +kernel
theorem fusedMap1656swap_checked : acceptsGraphIso
    (fused (graph core1656) (root 9) 1 0) DegreeOneSmallSpectrum1292.graph fusedMap1656swap=true := by decide +kernel
theorem certified1656swap : Certified (graph core1656) (root 9) 1 0 :=
  of_native_maps core1656 DegreeOneSmallSpectrum1892.graph DegreeOneSmallSpectrum1292.graph
    sourceMap1656swap fusedMap1656swap sourceMap1656swap_checked fusedMap1656swap_checked
    DegreeOneSmallComparisons.comparison1656
#print axioms sourceMap1656swap_checked
#print axioms fusedMap1656swap_checked
#print axioms certified1656swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
