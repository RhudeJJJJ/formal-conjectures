/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0349 : Family 6 := level6.get ⟨11,by decide⟩
def sourceMap0349 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (sourceLabel 6 0 1 v)
def fusedMap0349 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0349_checked : acceptsGraphIso
    (source (graph core0349) (root 6) 0 1) DegreeOneSmallSpectrum141.graph sourceMap0349=true := by decide +kernel
theorem fusedMap0349_checked : acceptsGraphIso
    (fused (graph core0349) (root 6) 0 1) DegreeOneSmallSpectrum082.graph fusedMap0349=true := by decide +kernel
theorem certified0349 : Certified (graph core0349) (root 6) 0 1 :=
  of_native_maps core0349 DegreeOneSmallSpectrum141.graph DegreeOneSmallSpectrum082.graph
    sourceMap0349 fusedMap0349 sourceMap0349_checked fusedMap0349_checked
    DegreeOneSmallComparisons.comparison0349
#print axioms sourceMap0349_checked
#print axioms fusedMap0349_checked
#print axioms certified0349
def sourceMap0349swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (sourceLabel 6 1 0 v)
def fusedMap0349swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0349swap_checked : acceptsGraphIso
    (source (graph core0349) (root 6) 1 0) DegreeOneSmallSpectrum141.graph sourceMap0349swap=true := by decide +kernel
theorem fusedMap0349swap_checked : acceptsGraphIso
    (fused (graph core0349) (root 6) 1 0) DegreeOneSmallSpectrum082.graph fusedMap0349swap=true := by decide +kernel
theorem certified0349swap : Certified (graph core0349) (root 6) 1 0 :=
  of_native_maps core0349 DegreeOneSmallSpectrum141.graph DegreeOneSmallSpectrum082.graph
    sourceMap0349swap fusedMap0349swap sourceMap0349swap_checked fusedMap0349swap_checked
    DegreeOneSmallComparisons.comparison0349
#print axioms sourceMap0349swap_checked
#print axioms fusedMap0349swap_checked
#print axioms certified0349swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
