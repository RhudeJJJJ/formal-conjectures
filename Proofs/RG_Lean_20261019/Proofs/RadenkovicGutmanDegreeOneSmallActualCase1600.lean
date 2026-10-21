/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1600 : Family 9 := level9.get ⟨338,by decide⟩
def sourceMap1600 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1600 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1600_checked : acceptsGraphIso
    (source (graph core1600) (root 9) 0 1) DegreeOneSmallSpectrum1665.graph sourceMap1600=true := by decide +kernel
theorem fusedMap1600_checked : acceptsGraphIso
    (fused (graph core1600) (root 9) 0 1) DegreeOneSmallSpectrum1023.graph fusedMap1600=true := by decide +kernel
theorem certified1600 : Certified (graph core1600) (root 9) 0 1 :=
  of_native_maps core1600 DegreeOneSmallSpectrum1665.graph DegreeOneSmallSpectrum1023.graph
    sourceMap1600 fusedMap1600 sourceMap1600_checked fusedMap1600_checked
    DegreeOneSmallComparisons.comparison1600
#print axioms sourceMap1600_checked
#print axioms fusedMap1600_checked
#print axioms certified1600
def sourceMap1600swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1600swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1600swap_checked : acceptsGraphIso
    (source (graph core1600) (root 9) 1 0) DegreeOneSmallSpectrum1665.graph sourceMap1600swap=true := by decide +kernel
theorem fusedMap1600swap_checked : acceptsGraphIso
    (fused (graph core1600) (root 9) 1 0) DegreeOneSmallSpectrum1023.graph fusedMap1600swap=true := by decide +kernel
theorem certified1600swap : Certified (graph core1600) (root 9) 1 0 :=
  of_native_maps core1600 DegreeOneSmallSpectrum1665.graph DegreeOneSmallSpectrum1023.graph
    sourceMap1600swap fusedMap1600swap sourceMap1600swap_checked fusedMap1600swap_checked
    DegreeOneSmallComparisons.comparison1600
#print axioms sourceMap1600swap_checked
#print axioms fusedMap1600swap_checked
#print axioms certified1600swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
