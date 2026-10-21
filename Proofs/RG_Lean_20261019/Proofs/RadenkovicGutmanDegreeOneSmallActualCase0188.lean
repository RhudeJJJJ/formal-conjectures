/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0188 : Family 5 := level5.get ⟨2,by decide⟩
def sourceMap0188 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap0188 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap0188_checked : acceptsGraphIso
    (source (graph core0188) (root 5) 0 5) DegreeOneSmallSpectrum935.graph sourceMap0188=true := by decide +kernel
theorem fusedMap0188_checked : acceptsGraphIso
    (fused (graph core0188) (root 5) 0 5) DegreeOneSmallSpectrum857.graph fusedMap0188=true := by decide +kernel
theorem certified0188 : Certified (graph core0188) (root 5) 0 5 :=
  of_native_maps core0188 DegreeOneSmallSpectrum935.graph DegreeOneSmallSpectrum857.graph
    sourceMap0188 fusedMap0188 sourceMap0188_checked fusedMap0188_checked
    DegreeOneSmallComparisons.comparison0188
#print axioms sourceMap0188_checked
#print axioms fusedMap0188_checked
#print axioms certified0188
def sourceMap0188swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,12,7] (sourceLabel 5 5 0 v)
def fusedMap0188swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap0188swap_checked : acceptsGraphIso
    (source (graph core0188) (root 5) 5 0) DegreeOneSmallSpectrum935.graph sourceMap0188swap=true := by decide +kernel
theorem fusedMap0188swap_checked : acceptsGraphIso
    (fused (graph core0188) (root 5) 5 0) DegreeOneSmallSpectrum857.graph fusedMap0188swap=true := by decide +kernel
theorem certified0188swap : Certified (graph core0188) (root 5) 5 0 :=
  of_native_maps core0188 DegreeOneSmallSpectrum935.graph DegreeOneSmallSpectrum857.graph
    sourceMap0188swap fusedMap0188swap sourceMap0188swap_checked fusedMap0188swap_checked
    DegreeOneSmallComparisons.comparison0188
#print axioms sourceMap0188swap_checked
#print axioms fusedMap0188swap_checked
#print axioms certified0188swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
