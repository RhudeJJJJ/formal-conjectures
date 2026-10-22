/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1108 : Family 8 := level8.get ⟨56,by decide⟩
def sourceMap1108 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1108 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1108_checked : acceptsGraphIso
    (source (graph core1108) (root 8) 0 2) DegreeOneSmallSpectrum1345.graph sourceMap1108=true := by decide +kernel
theorem fusedMap1108_checked : acceptsGraphIso
    (fused (graph core1108) (root 8) 0 2) DegreeOneSmallSpectrum914.graph fusedMap1108=true := by decide +kernel
theorem certified1108 : Certified (graph core1108) (root 8) 0 2 :=
  of_native_maps core1108 DegreeOneSmallSpectrum1345.graph DegreeOneSmallSpectrum914.graph
    sourceMap1108 fusedMap1108 sourceMap1108_checked fusedMap1108_checked
    DegreeTwoThreeFiniteComparisons.comparison1108
#print axioms sourceMap1108_checked
#print axioms fusedMap1108_checked
#print axioms certified1108
def sourceMap1108swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1108swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1108swap_checked : acceptsGraphIso
    (source (graph core1108) (root 8) 2 0) DegreeOneSmallSpectrum1345.graph sourceMap1108swap=true := by decide +kernel
theorem fusedMap1108swap_checked : acceptsGraphIso
    (fused (graph core1108) (root 8) 2 0) DegreeOneSmallSpectrum914.graph fusedMap1108swap=true := by decide +kernel
theorem certified1108swap : Certified (graph core1108) (root 8) 2 0 :=
  of_native_maps core1108 DegreeOneSmallSpectrum1345.graph DegreeOneSmallSpectrum914.graph
    sourceMap1108swap fusedMap1108swap sourceMap1108swap_checked fusedMap1108swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1108
#print axioms sourceMap1108swap_checked
#print axioms fusedMap1108swap_checked
#print axioms certified1108swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
