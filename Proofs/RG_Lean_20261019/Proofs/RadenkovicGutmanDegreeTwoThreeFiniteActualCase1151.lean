/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1151 : Family 8 := level8.get ⟨173,by decide⟩
def sourceMap1151 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,4,5,6,1,2,3] (sourceLabel 8 0 2 v)
def fusedMap1151 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (fusedLabel 8 0 2 v)
theorem sourceMap1151_checked : acceptsGraphIso
    (source (graph core1151) (root 8) 0 2) DegreeOneSmallSpectrum1483.graph sourceMap1151=true := by decide +kernel
theorem fusedMap1151_checked : acceptsGraphIso
    (fused (graph core1151) (root 8) 0 2) DegreeOneSmallSpectrum1500.graph fusedMap1151=true := by decide +kernel
theorem certified1151 : Certified (graph core1151) (root 8) 0 2 :=
  of_native_maps core1151 DegreeOneSmallSpectrum1483.graph DegreeOneSmallSpectrum1500.graph
    sourceMap1151 fusedMap1151 sourceMap1151_checked fusedMap1151_checked
    DegreeTwoThreeFiniteComparisons.comparison1151
#print axioms sourceMap1151_checked
#print axioms fusedMap1151_checked
#print axioms certified1151
def sourceMap1151swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,4,5,1,2,3,6] (sourceLabel 8 2 0 v)
def fusedMap1151swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (fusedLabel 8 2 0 v)
theorem sourceMap1151swap_checked : acceptsGraphIso
    (source (graph core1151) (root 8) 2 0) DegreeOneSmallSpectrum1483.graph sourceMap1151swap=true := by decide +kernel
theorem fusedMap1151swap_checked : acceptsGraphIso
    (fused (graph core1151) (root 8) 2 0) DegreeOneSmallSpectrum1500.graph fusedMap1151swap=true := by decide +kernel
theorem certified1151swap : Certified (graph core1151) (root 8) 2 0 :=
  of_native_maps core1151 DegreeOneSmallSpectrum1483.graph DegreeOneSmallSpectrum1500.graph
    sourceMap1151swap fusedMap1151swap sourceMap1151swap_checked fusedMap1151swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1151
#print axioms sourceMap1151swap_checked
#print axioms fusedMap1151swap_checked
#print axioms certified1151swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
