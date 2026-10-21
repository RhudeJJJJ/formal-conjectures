/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0322 : Family 6 := level6.get ⟨7,by decide⟩
def sourceMap0322 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (sourceLabel 6 0 1 v)
def fusedMap0322 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0322_checked : acceptsGraphIso
    (source (graph core0322) (root 6) 0 1) DegreeOneSmallSpectrum120.graph sourceMap0322=true := by decide +kernel
theorem fusedMap0322_checked : acceptsGraphIso
    (fused (graph core0322) (root 6) 0 1) DegreeOneSmallSpectrum075.graph fusedMap0322=true := by decide +kernel
theorem certified0322 : Certified (graph core0322) (root 6) 0 1 :=
  of_native_maps core0322 DegreeOneSmallSpectrum120.graph DegreeOneSmallSpectrum075.graph
    sourceMap0322 fusedMap0322 sourceMap0322_checked fusedMap0322_checked
    DegreeOneSmallComparisons.comparison0322
#print axioms sourceMap0322_checked
#print axioms fusedMap0322_checked
#print axioms certified0322
def sourceMap0322swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (sourceLabel 6 1 0 v)
def fusedMap0322swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0322swap_checked : acceptsGraphIso
    (source (graph core0322) (root 6) 1 0) DegreeOneSmallSpectrum120.graph sourceMap0322swap=true := by decide +kernel
theorem fusedMap0322swap_checked : acceptsGraphIso
    (fused (graph core0322) (root 6) 1 0) DegreeOneSmallSpectrum075.graph fusedMap0322swap=true := by decide +kernel
theorem certified0322swap : Certified (graph core0322) (root 6) 1 0 :=
  of_native_maps core0322 DegreeOneSmallSpectrum120.graph DegreeOneSmallSpectrum075.graph
    sourceMap0322swap fusedMap0322swap sourceMap0322swap_checked fusedMap0322swap_checked
    DegreeOneSmallComparisons.comparison0322
#print axioms sourceMap0322swap_checked
#print axioms fusedMap0322swap_checked
#print axioms certified0322swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
