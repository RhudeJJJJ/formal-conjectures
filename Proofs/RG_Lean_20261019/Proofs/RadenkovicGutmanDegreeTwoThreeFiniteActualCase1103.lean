/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1103 : Family 8 := level8.get ⟨38,by decide⟩
def sourceMap1103 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1103 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1103_checked : acceptsGraphIso
    (source (graph core1103) (root 8) 0 2) DegreeOneSmallSpectrum1079.graph sourceMap1103=true := by decide +kernel
theorem fusedMap1103_checked : acceptsGraphIso
    (fused (graph core1103) (root 8) 0 2) DegreeOneSmallSpectrum869.graph fusedMap1103=true := by decide +kernel
theorem certified1103 : Certified (graph core1103) (root 8) 0 2 :=
  of_native_maps core1103 DegreeOneSmallSpectrum1079.graph DegreeOneSmallSpectrum869.graph
    sourceMap1103 fusedMap1103 sourceMap1103_checked fusedMap1103_checked
    DegreeTwoThreeFiniteComparisons.comparison1103
#print axioms sourceMap1103_checked
#print axioms fusedMap1103_checked
#print axioms certified1103
def sourceMap1103swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1103swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1103swap_checked : acceptsGraphIso
    (source (graph core1103) (root 8) 2 0) DegreeOneSmallSpectrum1079.graph sourceMap1103swap=true := by decide +kernel
theorem fusedMap1103swap_checked : acceptsGraphIso
    (fused (graph core1103) (root 8) 2 0) DegreeOneSmallSpectrum869.graph fusedMap1103swap=true := by decide +kernel
theorem certified1103swap : Certified (graph core1103) (root 8) 2 0 :=
  of_native_maps core1103 DegreeOneSmallSpectrum1079.graph DegreeOneSmallSpectrum869.graph
    sourceMap1103swap fusedMap1103swap sourceMap1103swap_checked fusedMap1103swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1103
#print axioms sourceMap1103swap_checked
#print axioms fusedMap1103swap_checked
#print axioms certified1103swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
