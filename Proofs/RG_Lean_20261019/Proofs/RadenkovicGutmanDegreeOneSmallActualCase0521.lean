/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0521 : Family 7 := level7.get ⟨14,by decide⟩
def sourceMap0521 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0521 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0521_checked : acceptsGraphIso
    (source (graph core0521) (root 7) 0 2) DegreeOneSmallSpectrum549.graph sourceMap0521=true := by decide +kernel
theorem fusedMap0521_checked : acceptsGraphIso
    (fused (graph core0521) (root 7) 0 2) DegreeOneSmallSpectrum381.graph fusedMap0521=true := by decide +kernel
theorem certified0521 : Certified (graph core0521) (root 7) 0 2 :=
  of_native_maps core0521 DegreeOneSmallSpectrum549.graph DegreeOneSmallSpectrum381.graph
    sourceMap0521 fusedMap0521 sourceMap0521_checked fusedMap0521_checked
    DegreeOneSmallComparisons.comparison0521
#print axioms sourceMap0521_checked
#print axioms fusedMap0521_checked
#print axioms certified0521
def sourceMap0521swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0521swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0521swap_checked : acceptsGraphIso
    (source (graph core0521) (root 7) 2 0) DegreeOneSmallSpectrum549.graph sourceMap0521swap=true := by decide +kernel
theorem fusedMap0521swap_checked : acceptsGraphIso
    (fused (graph core0521) (root 7) 2 0) DegreeOneSmallSpectrum381.graph fusedMap0521swap=true := by decide +kernel
theorem certified0521swap : Certified (graph core0521) (root 7) 2 0 :=
  of_native_maps core0521 DegreeOneSmallSpectrum549.graph DegreeOneSmallSpectrum381.graph
    sourceMap0521swap fusedMap0521swap sourceMap0521swap_checked fusedMap0521swap_checked
    DegreeOneSmallComparisons.comparison0521
#print axioms sourceMap0521swap_checked
#print axioms fusedMap0521swap_checked
#print axioms certified0521swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
