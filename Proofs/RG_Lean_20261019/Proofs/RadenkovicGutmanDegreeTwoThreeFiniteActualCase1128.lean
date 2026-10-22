/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1128 : Family 8 := level8.get ⟨117,by decide⟩
def sourceMap1128 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1128 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1128_checked : acceptsGraphIso
    (source (graph core1128) (root 8) 0 2) DegreeOneSmallSpectrum1156.graph sourceMap1128=true := by decide +kernel
theorem fusedMap1128_checked : acceptsGraphIso
    (fused (graph core1128) (root 8) 0 2) DegreeOneSmallSpectrum1158.graph fusedMap1128=true := by decide +kernel
theorem certified1128 : Certified (graph core1128) (root 8) 0 2 :=
  of_native_maps core1128 DegreeOneSmallSpectrum1156.graph DegreeOneSmallSpectrum1158.graph
    sourceMap1128 fusedMap1128 sourceMap1128_checked fusedMap1128_checked
    DegreeTwoThreeFiniteComparisons.comparison1128
#print axioms sourceMap1128_checked
#print axioms fusedMap1128_checked
#print axioms certified1128
def sourceMap1128swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1128swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1128swap_checked : acceptsGraphIso
    (source (graph core1128) (root 8) 2 0) DegreeOneSmallSpectrum1156.graph sourceMap1128swap=true := by decide +kernel
theorem fusedMap1128swap_checked : acceptsGraphIso
    (fused (graph core1128) (root 8) 2 0) DegreeOneSmallSpectrum1158.graph fusedMap1128swap=true := by decide +kernel
theorem certified1128swap : Certified (graph core1128) (root 8) 2 0 :=
  of_native_maps core1128 DegreeOneSmallSpectrum1156.graph DegreeOneSmallSpectrum1158.graph
    sourceMap1128swap fusedMap1128swap sourceMap1128swap_checked fusedMap1128swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1128
#print axioms sourceMap1128swap_checked
#print axioms fusedMap1128swap_checked
#print axioms certified1128swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
