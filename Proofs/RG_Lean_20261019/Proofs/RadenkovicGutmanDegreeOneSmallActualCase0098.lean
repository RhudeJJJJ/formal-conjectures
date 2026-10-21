/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0098 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0098 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,9,5,6,7,8] (sourceLabel 4 0 3 v)
def fusedMap0098 : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 4 0 3 v)
theorem sourceMap0098_checked : acceptsGraphIso
    (source (graph core0098) (root 4) 0 3) DegreeOneSmallSpectrum091.graph sourceMap0098=true := by decide +kernel
theorem fusedMap0098_checked : acceptsGraphIso
    (fused (graph core0098) (root 4) 0 3) DegreeOneSmallSpectrum073.graph fusedMap0098=true := by decide +kernel
theorem certified0098 : Certified (graph core0098) (root 4) 0 3 :=
  of_native_maps core0098 DegreeOneSmallSpectrum091.graph DegreeOneSmallSpectrum073.graph
    sourceMap0098 fusedMap0098 sourceMap0098_checked fusedMap0098_checked
    DegreeOneSmallComparisons.comparison0098
#print axioms sourceMap0098_checked
#print axioms fusedMap0098_checked
#print axioms certified0098
def sourceMap0098swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 4 3 0 v)
def fusedMap0098swap : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 4 3 0 v)
theorem sourceMap0098swap_checked : acceptsGraphIso
    (source (graph core0098) (root 4) 3 0) DegreeOneSmallSpectrum091.graph sourceMap0098swap=true := by decide +kernel
theorem fusedMap0098swap_checked : acceptsGraphIso
    (fused (graph core0098) (root 4) 3 0) DegreeOneSmallSpectrum073.graph fusedMap0098swap=true := by decide +kernel
theorem certified0098swap : Certified (graph core0098) (root 4) 3 0 :=
  of_native_maps core0098 DegreeOneSmallSpectrum091.graph DegreeOneSmallSpectrum073.graph
    sourceMap0098swap fusedMap0098swap sourceMap0098swap_checked fusedMap0098swap_checked
    DegreeOneSmallComparisons.comparison0098
#print axioms sourceMap0098swap_checked
#print axioms fusedMap0098swap_checked
#print axioms certified0098swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
