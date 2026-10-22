/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1094 : Family 7 := level7.get ⟨102,by decide⟩
def sourceMap1094 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 0 2 v)
def fusedMap1094 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1094_checked : acceptsGraphIso
    (source (graph core1094) (root 7) 0 2) DegreeOneSmallSpectrum605.graph sourceMap1094=true := by decide +kernel
theorem fusedMap1094_checked : acceptsGraphIso
    (fused (graph core1094) (root 7) 0 2) DegreeOneSmallSpectrum608.graph fusedMap1094=true := by decide +kernel
theorem certified1094 : Certified (graph core1094) (root 7) 0 2 :=
  of_native_maps core1094 DegreeOneSmallSpectrum605.graph DegreeOneSmallSpectrum608.graph
    sourceMap1094 fusedMap1094 sourceMap1094_checked fusedMap1094_checked
    DegreeTwoThreeFiniteComparisons.comparison1094
#print axioms sourceMap1094_checked
#print axioms fusedMap1094_checked
#print axioms certified1094
def sourceMap1094swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,8] (sourceLabel 7 2 0 v)
def fusedMap1094swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1094swap_checked : acceptsGraphIso
    (source (graph core1094) (root 7) 2 0) DegreeOneSmallSpectrum605.graph sourceMap1094swap=true := by decide +kernel
theorem fusedMap1094swap_checked : acceptsGraphIso
    (fused (graph core1094) (root 7) 2 0) DegreeOneSmallSpectrum608.graph fusedMap1094swap=true := by decide +kernel
theorem certified1094swap : Certified (graph core1094) (root 7) 2 0 :=
  of_native_maps core1094 DegreeOneSmallSpectrum605.graph DegreeOneSmallSpectrum608.graph
    sourceMap1094swap fusedMap1094swap sourceMap1094swap_checked fusedMap1094swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1094
#print axioms sourceMap1094swap_checked
#print axioms fusedMap1094swap_checked
#print axioms certified1094swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
