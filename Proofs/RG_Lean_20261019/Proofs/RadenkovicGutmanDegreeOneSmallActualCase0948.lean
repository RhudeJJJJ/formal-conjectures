/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0948 : Family 8 := level8.get ⟨73,by decide⟩
def sourceMap0948 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0948 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 0 1 v)
theorem sourceMap0948_checked : acceptsGraphIso
    (source (graph core0948) (root 8) 0 1) DegreeOneSmallSpectrum547.graph sourceMap0948=true := by decide +kernel
theorem fusedMap0948_checked : acceptsGraphIso
    (fused (graph core0948) (root 8) 0 1) DegreeOneSmallSpectrum575.graph fusedMap0948=true := by decide +kernel
theorem certified0948 : Certified (graph core0948) (root 8) 0 1 :=
  of_native_maps core0948 DegreeOneSmallSpectrum547.graph DegreeOneSmallSpectrum575.graph
    sourceMap0948 fusedMap0948 sourceMap0948_checked fusedMap0948_checked
    DegreeOneSmallComparisons.comparison0948
#print axioms sourceMap0948_checked
#print axioms fusedMap0948_checked
#print axioms certified0948
def sourceMap0948swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0948swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 1 0 v)
theorem sourceMap0948swap_checked : acceptsGraphIso
    (source (graph core0948) (root 8) 1 0) DegreeOneSmallSpectrum547.graph sourceMap0948swap=true := by decide +kernel
theorem fusedMap0948swap_checked : acceptsGraphIso
    (fused (graph core0948) (root 8) 1 0) DegreeOneSmallSpectrum575.graph fusedMap0948swap=true := by decide +kernel
theorem certified0948swap : Certified (graph core0948) (root 8) 1 0 :=
  of_native_maps core0948 DegreeOneSmallSpectrum547.graph DegreeOneSmallSpectrum575.graph
    sourceMap0948swap fusedMap0948swap sourceMap0948swap_checked fusedMap0948swap_checked
    DegreeOneSmallComparisons.comparison0948
#print axioms sourceMap0948swap_checked
#print axioms fusedMap0948swap_checked
#print axioms certified0948swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
