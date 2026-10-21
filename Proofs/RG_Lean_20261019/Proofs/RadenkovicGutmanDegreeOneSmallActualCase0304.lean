/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0304 : Family 6 := level6.get ⟨4,by decide⟩
def sourceMap0304 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,5,4,2,3] (sourceLabel 6 0 1 v)
def fusedMap0304 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (fusedLabel 6 0 1 v)
theorem sourceMap0304_checked : acceptsGraphIso
    (source (graph core0304) (root 6) 0 1) DegreeOneSmallSpectrum083.graph sourceMap0304=true := by decide +kernel
theorem fusedMap0304_checked : acceptsGraphIso
    (fused (graph core0304) (root 6) 0 1) DegreeOneSmallSpectrum091.graph fusedMap0304=true := by decide +kernel
theorem certified0304 : Certified (graph core0304) (root 6) 0 1 :=
  of_native_maps core0304 DegreeOneSmallSpectrum083.graph DegreeOneSmallSpectrum091.graph
    sourceMap0304 fusedMap0304 sourceMap0304_checked fusedMap0304_checked
    DegreeOneSmallComparisons.comparison0304
#print axioms sourceMap0304_checked
#print axioms fusedMap0304_checked
#print axioms certified0304
def sourceMap0304swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,5,2,3,4] (sourceLabel 6 1 0 v)
def fusedMap0304swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (fusedLabel 6 1 0 v)
theorem sourceMap0304swap_checked : acceptsGraphIso
    (source (graph core0304) (root 6) 1 0) DegreeOneSmallSpectrum083.graph sourceMap0304swap=true := by decide +kernel
theorem fusedMap0304swap_checked : acceptsGraphIso
    (fused (graph core0304) (root 6) 1 0) DegreeOneSmallSpectrum091.graph fusedMap0304swap=true := by decide +kernel
theorem certified0304swap : Certified (graph core0304) (root 6) 1 0 :=
  of_native_maps core0304 DegreeOneSmallSpectrum083.graph DegreeOneSmallSpectrum091.graph
    sourceMap0304swap fusedMap0304swap sourceMap0304swap_checked fusedMap0304swap_checked
    DegreeOneSmallComparisons.comparison0304
#print axioms sourceMap0304swap_checked
#print axioms fusedMap0304swap_checked
#print axioms certified0304swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
