/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1398 : Family 9 := level9.get ⟨144,by decide⟩
def sourceMap1398 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1398 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1398_checked : acceptsGraphIso
    (source (graph core1398) (root 9) 0 1) DegreeOneSmallSpectrum1025.graph sourceMap1398=true := by decide +kernel
theorem fusedMap1398_checked : acceptsGraphIso
    (fused (graph core1398) (root 9) 0 1) DegreeOneSmallSpectrum1027.graph fusedMap1398=true := by decide +kernel
theorem certified1398 : Certified (graph core1398) (root 9) 0 1 :=
  of_native_maps core1398 DegreeOneSmallSpectrum1025.graph DegreeOneSmallSpectrum1027.graph
    sourceMap1398 fusedMap1398 sourceMap1398_checked fusedMap1398_checked
    DegreeOneSmallComparisons.comparison1398
#print axioms sourceMap1398_checked
#print axioms fusedMap1398_checked
#print axioms certified1398
def sourceMap1398swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1398swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1398swap_checked : acceptsGraphIso
    (source (graph core1398) (root 9) 1 0) DegreeOneSmallSpectrum1025.graph sourceMap1398swap=true := by decide +kernel
theorem fusedMap1398swap_checked : acceptsGraphIso
    (fused (graph core1398) (root 9) 1 0) DegreeOneSmallSpectrum1027.graph fusedMap1398swap=true := by decide +kernel
theorem certified1398swap : Certified (graph core1398) (root 9) 1 0 :=
  of_native_maps core1398 DegreeOneSmallSpectrum1025.graph DegreeOneSmallSpectrum1027.graph
    sourceMap1398swap fusedMap1398swap sourceMap1398swap_checked fusedMap1398swap_checked
    DegreeOneSmallComparisons.comparison1398
#print axioms sourceMap1398swap_checked
#print axioms fusedMap1398swap_checked
#print axioms certified1398swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
