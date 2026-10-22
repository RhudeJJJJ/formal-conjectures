/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1063 : Family 7 := level7.get ⟨23,by decide⟩
def sourceMap1063 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 7 0 2 v)
def fusedMap1063 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,5,1,2,3,4] (fusedLabel 7 0 2 v)
theorem sourceMap1063_checked : acceptsGraphIso
    (source (graph core1063) (root 7) 0 2) DegreeOneSmallSpectrum581.graph sourceMap1063=true := by decide +kernel
theorem fusedMap1063_checked : acceptsGraphIso
    (fused (graph core1063) (root 7) 0 2) DegreeOneSmallSpectrum395.graph fusedMap1063=true := by decide +kernel
theorem certified1063 : Certified (graph core1063) (root 7) 0 2 :=
  of_native_maps core1063 DegreeOneSmallSpectrum581.graph DegreeOneSmallSpectrum395.graph
    sourceMap1063 fusedMap1063 sourceMap1063_checked fusedMap1063_checked
    DegreeTwoThreeFiniteComparisons.comparison1063
#print axioms sourceMap1063_checked
#print axioms fusedMap1063_checked
#print axioms certified1063
def sourceMap1063swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,2,3,4,6] (sourceLabel 7 2 0 v)
def fusedMap1063swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,5,1,2,3,4] (fusedLabel 7 2 0 v)
theorem sourceMap1063swap_checked : acceptsGraphIso
    (source (graph core1063) (root 7) 2 0) DegreeOneSmallSpectrum581.graph sourceMap1063swap=true := by decide +kernel
theorem fusedMap1063swap_checked : acceptsGraphIso
    (fused (graph core1063) (root 7) 2 0) DegreeOneSmallSpectrum395.graph fusedMap1063swap=true := by decide +kernel
theorem certified1063swap : Certified (graph core1063) (root 7) 2 0 :=
  of_native_maps core1063 DegreeOneSmallSpectrum581.graph DegreeOneSmallSpectrum395.graph
    sourceMap1063swap fusedMap1063swap sourceMap1063swap_checked fusedMap1063swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1063
#print axioms sourceMap1063swap_checked
#print axioms fusedMap1063swap_checked
#print axioms certified1063swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
