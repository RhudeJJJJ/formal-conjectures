/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0449 : Family 7 := level7.get ⟨0,by decide⟩
def sourceMap0449 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 7 0 2 v)
def fusedMap0449 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 7 0 2 v)
theorem sourceMap0449_checked : acceptsGraphIso
    (source (graph core0449) (root 7) 0 2) DegreeOneSmallSpectrum392.graph sourceMap0449=true := by decide +kernel
theorem fusedMap0449_checked : acceptsGraphIso
    (fused (graph core0449) (root 7) 0 2) DegreeOneSmallSpectrum369.graph fusedMap0449=true := by decide +kernel
theorem certified0449 : Certified (graph core0449) (root 7) 0 2 :=
  of_native_maps core0449 DegreeOneSmallSpectrum392.graph DegreeOneSmallSpectrum369.graph
    sourceMap0449 fusedMap0449 sourceMap0449_checked fusedMap0449_checked
    DegreeOneSmallComparisons.comparison0449
#print axioms sourceMap0449_checked
#print axioms fusedMap0449_checked
#print axioms certified0449
def sourceMap0449swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,3,4,5,6] (sourceLabel 7 2 0 v)
def fusedMap0449swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 7 2 0 v)
theorem sourceMap0449swap_checked : acceptsGraphIso
    (source (graph core0449) (root 7) 2 0) DegreeOneSmallSpectrum392.graph sourceMap0449swap=true := by decide +kernel
theorem fusedMap0449swap_checked : acceptsGraphIso
    (fused (graph core0449) (root 7) 2 0) DegreeOneSmallSpectrum369.graph fusedMap0449swap=true := by decide +kernel
theorem certified0449swap : Certified (graph core0449) (root 7) 2 0 :=
  of_native_maps core0449 DegreeOneSmallSpectrum392.graph DegreeOneSmallSpectrum369.graph
    sourceMap0449swap fusedMap0449swap sourceMap0449swap_checked fusedMap0449swap_checked
    DegreeOneSmallComparisons.comparison0449
#print axioms sourceMap0449swap_checked
#print axioms fusedMap0449swap_checked
#print axioms certified0449swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
