/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0503 : Family 7 := level7.get ⟨10,by decide⟩
def sourceMap0503 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,10,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap0503 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0503_checked : acceptsGraphIso
    (source (graph core0503) (root 7) 0 2) DegreeOneSmallSpectrum497.graph sourceMap0503=true := by decide +kernel
theorem fusedMap0503_checked : acceptsGraphIso
    (fused (graph core0503) (root 7) 0 2) DegreeOneSmallSpectrum373.graph fusedMap0503=true := by decide +kernel
theorem certified0503 : Certified (graph core0503) (root 7) 0 2 :=
  of_native_maps core0503 DegreeOneSmallSpectrum497.graph DegreeOneSmallSpectrum373.graph
    sourceMap0503 fusedMap0503 sourceMap0503_checked fusedMap0503_checked
    DegreeOneSmallComparisons.comparison0503
#print axioms sourceMap0503_checked
#print axioms fusedMap0503_checked
#print axioms certified0503
def sourceMap0503swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (sourceLabel 7 2 0 v)
def fusedMap0503swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0503swap_checked : acceptsGraphIso
    (source (graph core0503) (root 7) 2 0) DegreeOneSmallSpectrum497.graph sourceMap0503swap=true := by decide +kernel
theorem fusedMap0503swap_checked : acceptsGraphIso
    (fused (graph core0503) (root 7) 2 0) DegreeOneSmallSpectrum373.graph fusedMap0503swap=true := by decide +kernel
theorem certified0503swap : Certified (graph core0503) (root 7) 2 0 :=
  of_native_maps core0503 DegreeOneSmallSpectrum497.graph DegreeOneSmallSpectrum373.graph
    sourceMap0503swap fusedMap0503swap sourceMap0503swap_checked fusedMap0503swap_checked
    DegreeOneSmallComparisons.comparison0503
#print axioms sourceMap0503swap_checked
#print axioms fusedMap0503swap_checked
#print axioms certified0503swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
