/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1111 : Family 8 := level8.get ⟨67,by decide⟩
def sourceMap1111 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,12,10,11,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap1111 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1111_checked : acceptsGraphIso
    (source (graph core1111) (root 8) 0 2) DegreeOneSmallSpectrum1449.graph sourceMap1111=true := by decide +kernel
theorem fusedMap1111_checked : acceptsGraphIso
    (fused (graph core1111) (root 8) 0 2) DegreeOneSmallSpectrum934.graph fusedMap1111=true := by decide +kernel
theorem certified1111 : Certified (graph core1111) (root 8) 0 2 :=
  of_native_maps core1111 DegreeOneSmallSpectrum1449.graph DegreeOneSmallSpectrum934.graph
    sourceMap1111 fusedMap1111 sourceMap1111_checked fusedMap1111_checked
    DegreeTwoThreeFiniteComparisons.comparison1111
#print axioms sourceMap1111_checked
#print axioms fusedMap1111_checked
#print axioms certified1111
def sourceMap1111swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,12,10,7,8,9,11] (sourceLabel 8 2 0 v)
def fusedMap1111swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1111swap_checked : acceptsGraphIso
    (source (graph core1111) (root 8) 2 0) DegreeOneSmallSpectrum1449.graph sourceMap1111swap=true := by decide +kernel
theorem fusedMap1111swap_checked : acceptsGraphIso
    (fused (graph core1111) (root 8) 2 0) DegreeOneSmallSpectrum934.graph fusedMap1111swap=true := by decide +kernel
theorem certified1111swap : Certified (graph core1111) (root 8) 2 0 :=
  of_native_maps core1111 DegreeOneSmallSpectrum1449.graph DegreeOneSmallSpectrum934.graph
    sourceMap1111swap fusedMap1111swap sourceMap1111swap_checked fusedMap1111swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1111
#print axioms sourceMap1111swap_checked
#print axioms fusedMap1111swap_checked
#print axioms certified1111swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
