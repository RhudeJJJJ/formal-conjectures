/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1622 : Family 9 := level9.get ⟨362,by decide⟩
def sourceMap1622 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1622 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1622_checked : acceptsGraphIso
    (source (graph core1622) (root 9) 0 1) DegreeOneSmallSpectrum1769.graph sourceMap1622=true := by decide +kernel
theorem fusedMap1622_checked : acceptsGraphIso
    (fused (graph core1622) (root 9) 0 1) DegreeOneSmallSpectrum1097.graph fusedMap1622=true := by decide +kernel
theorem certified1622 : Certified (graph core1622) (root 9) 0 1 :=
  of_native_maps core1622 DegreeOneSmallSpectrum1769.graph DegreeOneSmallSpectrum1097.graph
    sourceMap1622 fusedMap1622 sourceMap1622_checked fusedMap1622_checked
    DegreeOneSmallComparisons.comparison1622
#print axioms sourceMap1622_checked
#print axioms fusedMap1622_checked
#print axioms certified1622
def sourceMap1622swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1622swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1622swap_checked : acceptsGraphIso
    (source (graph core1622) (root 9) 1 0) DegreeOneSmallSpectrum1769.graph sourceMap1622swap=true := by decide +kernel
theorem fusedMap1622swap_checked : acceptsGraphIso
    (fused (graph core1622) (root 9) 1 0) DegreeOneSmallSpectrum1097.graph fusedMap1622swap=true := by decide +kernel
theorem certified1622swap : Certified (graph core1622) (root 9) 1 0 :=
  of_native_maps core1622 DegreeOneSmallSpectrum1769.graph DegreeOneSmallSpectrum1097.graph
    sourceMap1622swap fusedMap1622swap sourceMap1622swap_checked fusedMap1622swap_checked
    DegreeOneSmallComparisons.comparison1622
#print axioms sourceMap1622swap_checked
#print axioms fusedMap1622swap_checked
#print axioms certified1622swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
