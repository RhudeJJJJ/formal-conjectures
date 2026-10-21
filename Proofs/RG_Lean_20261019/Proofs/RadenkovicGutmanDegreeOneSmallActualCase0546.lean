/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0546 : Family 7 := level7.get ⟨19,by decide⟩
def sourceMap0546 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0546 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0546_checked : acceptsGraphIso
    (source (graph core0546) (root 7) 0 3) DegreeOneSmallSpectrum960.graph sourceMap0546=true := by decide +kernel
theorem fusedMap0546_checked : acceptsGraphIso
    (fused (graph core0546) (root 7) 0 3) DegreeOneSmallSpectrum961.graph fusedMap0546=true := by decide +kernel
theorem certified0546 : Certified (graph core0546) (root 7) 0 3 :=
  of_native_maps core0546 DegreeOneSmallSpectrum960.graph DegreeOneSmallSpectrum961.graph
    sourceMap0546 fusedMap0546 sourceMap0546_checked fusedMap0546_checked
    DegreeOneSmallComparisons.comparison0546
#print axioms sourceMap0546_checked
#print axioms fusedMap0546_checked
#print axioms certified0546
def sourceMap0546swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0546swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0546swap_checked : acceptsGraphIso
    (source (graph core0546) (root 7) 3 0) DegreeOneSmallSpectrum960.graph sourceMap0546swap=true := by decide +kernel
theorem fusedMap0546swap_checked : acceptsGraphIso
    (fused (graph core0546) (root 7) 3 0) DegreeOneSmallSpectrum961.graph fusedMap0546swap=true := by decide +kernel
theorem certified0546swap : Certified (graph core0546) (root 7) 3 0 :=
  of_native_maps core0546 DegreeOneSmallSpectrum960.graph DegreeOneSmallSpectrum961.graph
    sourceMap0546swap fusedMap0546swap sourceMap0546swap_checked fusedMap0546swap_checked
    DegreeOneSmallComparisons.comparison0546
#print axioms sourceMap0546swap_checked
#print axioms fusedMap0546swap_checked
#print axioms certified0546swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
