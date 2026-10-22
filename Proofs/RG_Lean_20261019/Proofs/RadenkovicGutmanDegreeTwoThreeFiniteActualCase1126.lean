/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1126 : Family 8 := level8.get ⟨111,by decide⟩
def sourceMap1126 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1126 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1126_checked : acceptsGraphIso
    (source (graph core1126) (root 8) 0 2) DegreeOneSmallSpectrum1110.graph sourceMap1126=true := by decide +kernel
theorem fusedMap1126_checked : acceptsGraphIso
    (fused (graph core1126) (root 8) 0 2) DegreeOneSmallSpectrum1112.graph fusedMap1126=true := by decide +kernel
theorem certified1126 : Certified (graph core1126) (root 8) 0 2 :=
  of_native_maps core1126 DegreeOneSmallSpectrum1110.graph DegreeOneSmallSpectrum1112.graph
    sourceMap1126 fusedMap1126 sourceMap1126_checked fusedMap1126_checked
    DegreeTwoThreeFiniteComparisons.comparison1126
#print axioms sourceMap1126_checked
#print axioms fusedMap1126_checked
#print axioms certified1126
def sourceMap1126swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1126swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1126swap_checked : acceptsGraphIso
    (source (graph core1126) (root 8) 2 0) DegreeOneSmallSpectrum1110.graph sourceMap1126swap=true := by decide +kernel
theorem fusedMap1126swap_checked : acceptsGraphIso
    (fused (graph core1126) (root 8) 2 0) DegreeOneSmallSpectrum1112.graph fusedMap1126swap=true := by decide +kernel
theorem certified1126swap : Certified (graph core1126) (root 8) 2 0 :=
  of_native_maps core1126 DegreeOneSmallSpectrum1110.graph DegreeOneSmallSpectrum1112.graph
    sourceMap1126swap fusedMap1126swap sourceMap1126swap_checked fusedMap1126swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1126
#print axioms sourceMap1126swap_checked
#print axioms fusedMap1126swap_checked
#print axioms certified1126swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
