/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1114 : Family 8 := level8.get ⟨77,by decide⟩
def sourceMap1114 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap1114 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1114_checked : acceptsGraphIso
    (source (graph core1114) (root 8) 0 2) DegreeOneSmallSpectrum1498.graph sourceMap1114=true := by decide +kernel
theorem fusedMap1114_checked : acceptsGraphIso
    (fused (graph core1114) (root 8) 0 2) DegreeOneSmallSpectrum955.graph fusedMap1114=true := by decide +kernel
theorem certified1114 : Certified (graph core1114) (root 8) 0 2 :=
  of_native_maps core1114 DegreeOneSmallSpectrum1498.graph DegreeOneSmallSpectrum955.graph
    sourceMap1114 fusedMap1114 sourceMap1114_checked fusedMap1114_checked
    DegreeTwoThreeFiniteComparisons.comparison1114
#print axioms sourceMap1114_checked
#print axioms fusedMap1114_checked
#print axioms certified1114
def sourceMap1114swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,2,3,4,6] (sourceLabel 8 2 0 v)
def fusedMap1114swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1114swap_checked : acceptsGraphIso
    (source (graph core1114) (root 8) 2 0) DegreeOneSmallSpectrum1498.graph sourceMap1114swap=true := by decide +kernel
theorem fusedMap1114swap_checked : acceptsGraphIso
    (fused (graph core1114) (root 8) 2 0) DegreeOneSmallSpectrum955.graph fusedMap1114swap=true := by decide +kernel
theorem certified1114swap : Certified (graph core1114) (root 8) 2 0 :=
  of_native_maps core1114 DegreeOneSmallSpectrum1498.graph DegreeOneSmallSpectrum955.graph
    sourceMap1114swap fusedMap1114swap sourceMap1114swap_checked fusedMap1114swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1114
#print axioms sourceMap1114swap_checked
#print axioms fusedMap1114swap_checked
#print axioms certified1114swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
