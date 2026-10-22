/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1110 : Family 8 := level8.get ⟨64,by decide⟩
def sourceMap1110 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1110 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1110_checked : acceptsGraphIso
    (source (graph core1110) (root 8) 0 2) DegreeOneSmallSpectrum1432.graph sourceMap1110=true := by decide +kernel
theorem fusedMap1110_checked : acceptsGraphIso
    (fused (graph core1110) (root 8) 0 2) DegreeOneSmallSpectrum928.graph fusedMap1110=true := by decide +kernel
theorem certified1110 : Certified (graph core1110) (root 8) 0 2 :=
  of_native_maps core1110 DegreeOneSmallSpectrum1432.graph DegreeOneSmallSpectrum928.graph
    sourceMap1110 fusedMap1110 sourceMap1110_checked fusedMap1110_checked
    DegreeTwoThreeFiniteComparisons.comparison1110
#print axioms sourceMap1110_checked
#print axioms fusedMap1110_checked
#print axioms certified1110
def sourceMap1110swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1110swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1110swap_checked : acceptsGraphIso
    (source (graph core1110) (root 8) 2 0) DegreeOneSmallSpectrum1432.graph sourceMap1110swap=true := by decide +kernel
theorem fusedMap1110swap_checked : acceptsGraphIso
    (fused (graph core1110) (root 8) 2 0) DegreeOneSmallSpectrum928.graph fusedMap1110swap=true := by decide +kernel
theorem certified1110swap : Certified (graph core1110) (root 8) 2 0 :=
  of_native_maps core1110 DegreeOneSmallSpectrum1432.graph DegreeOneSmallSpectrum928.graph
    sourceMap1110swap fusedMap1110swap sourceMap1110swap_checked fusedMap1110swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1110
#print axioms sourceMap1110swap_checked
#print axioms fusedMap1110swap_checked
#print axioms certified1110swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
