/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0781 : Family 8 := level8.get ⟨12,by decide⟩
def sourceMap0781 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,11,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap0781 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap0781_checked : acceptsGraphIso
    (source (graph core0781) (root 8) 0 2) DegreeOneSmallSpectrum903.graph sourceMap0781=true := by decide +kernel
theorem fusedMap0781_checked : acceptsGraphIso
    (fused (graph core0781) (root 8) 0 2) DegreeOneSmallSpectrum908.graph fusedMap0781=true := by decide +kernel
theorem certified0781 : Certified (graph core0781) (root 8) 0 2 :=
  of_native_maps core0781 DegreeOneSmallSpectrum903.graph DegreeOneSmallSpectrum908.graph
    sourceMap0781 fusedMap0781 sourceMap0781_checked fusedMap0781_checked
    DegreeOneSmallComparisons.comparison0781
#print axioms sourceMap0781_checked
#print axioms fusedMap0781_checked
#print axioms certified0781
def sourceMap0781swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (sourceLabel 8 2 0 v)
def fusedMap0781swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap0781swap_checked : acceptsGraphIso
    (source (graph core0781) (root 8) 2 0) DegreeOneSmallSpectrum903.graph sourceMap0781swap=true := by decide +kernel
theorem fusedMap0781swap_checked : acceptsGraphIso
    (fused (graph core0781) (root 8) 2 0) DegreeOneSmallSpectrum908.graph fusedMap0781swap=true := by decide +kernel
theorem certified0781swap : Certified (graph core0781) (root 8) 2 0 :=
  of_native_maps core0781 DegreeOneSmallSpectrum903.graph DegreeOneSmallSpectrum908.graph
    sourceMap0781swap fusedMap0781swap sourceMap0781swap_checked fusedMap0781swap_checked
    DegreeOneSmallComparisons.comparison0781
#print axioms sourceMap0781swap_checked
#print axioms fusedMap0781swap_checked
#print axioms certified0781swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
