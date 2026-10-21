/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0334 : Family 6 := level6.get ⟨8,by decide⟩
def sourceMap0334 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0334 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0334_checked : acceptsGraphIso
    (source (graph core0334) (root 6) 0 4) DegreeOneSmallSpectrum882.graph sourceMap0334=true := by decide +kernel
theorem fusedMap0334_checked : acceptsGraphIso
    (fused (graph core0334) (root 6) 0 4) DegreeOneSmallSpectrum887.graph fusedMap0334=true := by decide +kernel
theorem certified0334 : Certified (graph core0334) (root 6) 0 4 :=
  of_native_maps core0334 DegreeOneSmallSpectrum882.graph DegreeOneSmallSpectrum887.graph
    sourceMap0334 fusedMap0334 sourceMap0334_checked fusedMap0334_checked
    DegreeOneSmallComparisons.comparison0334
#print axioms sourceMap0334_checked
#print axioms fusedMap0334_checked
#print axioms certified0334
def sourceMap0334swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,12,7] (sourceLabel 6 4 0 v)
def fusedMap0334swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0334swap_checked : acceptsGraphIso
    (source (graph core0334) (root 6) 4 0) DegreeOneSmallSpectrum882.graph sourceMap0334swap=true := by decide +kernel
theorem fusedMap0334swap_checked : acceptsGraphIso
    (fused (graph core0334) (root 6) 4 0) DegreeOneSmallSpectrum887.graph fusedMap0334swap=true := by decide +kernel
theorem certified0334swap : Certified (graph core0334) (root 6) 4 0 :=
  of_native_maps core0334 DegreeOneSmallSpectrum882.graph DegreeOneSmallSpectrum887.graph
    sourceMap0334swap fusedMap0334swap sourceMap0334swap_checked fusedMap0334swap_checked
    DegreeOneSmallComparisons.comparison0334
#print axioms sourceMap0334swap_checked
#print axioms fusedMap0334swap_checked
#print axioms certified0334swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
