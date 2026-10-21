/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0367 : Family 6 := level6.get ⟨14,by decide⟩
def sourceMap0367 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,4,2,3] (sourceLabel 6 0 1 v)
def fusedMap0367 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0367_checked : acceptsGraphIso
    (source (graph core0367) (root 6) 0 1) DegreeOneSmallSpectrum144.graph sourceMap0367=true := by decide +kernel
theorem fusedMap0367_checked : acceptsGraphIso
    (fused (graph core0367) (root 6) 0 1) DegreeOneSmallSpectrum087.graph fusedMap0367=true := by decide +kernel
theorem certified0367 : Certified (graph core0367) (root 6) 0 1 :=
  of_native_maps core0367 DegreeOneSmallSpectrum144.graph DegreeOneSmallSpectrum087.graph
    sourceMap0367 fusedMap0367 sourceMap0367_checked fusedMap0367_checked
    DegreeOneSmallComparisons.comparison0367
#print axioms sourceMap0367_checked
#print axioms fusedMap0367_checked
#print axioms certified0367
def sourceMap0367swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (sourceLabel 6 1 0 v)
def fusedMap0367swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0367swap_checked : acceptsGraphIso
    (source (graph core0367) (root 6) 1 0) DegreeOneSmallSpectrum144.graph sourceMap0367swap=true := by decide +kernel
theorem fusedMap0367swap_checked : acceptsGraphIso
    (fused (graph core0367) (root 6) 1 0) DegreeOneSmallSpectrum087.graph fusedMap0367swap=true := by decide +kernel
theorem certified0367swap : Certified (graph core0367) (root 6) 1 0 :=
  of_native_maps core0367 DegreeOneSmallSpectrum144.graph DegreeOneSmallSpectrum087.graph
    sourceMap0367swap fusedMap0367swap sourceMap0367swap_checked fusedMap0367swap_checked
    DegreeOneSmallComparisons.comparison0367
#print axioms sourceMap0367swap_checked
#print axioms fusedMap0367swap_checked
#print axioms certified0367swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
