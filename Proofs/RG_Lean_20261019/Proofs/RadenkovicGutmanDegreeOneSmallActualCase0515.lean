/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0515 : Family 7 := level7.get ⟨13,by decide⟩
def sourceMap0515 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0515 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0515_checked : acceptsGraphIso
    (source (graph core0515) (root 7) 0 2) DegreeOneSmallSpectrum533.graph sourceMap0515=true := by decide +kernel
theorem fusedMap0515_checked : acceptsGraphIso
    (fused (graph core0515) (root 7) 0 2) DegreeOneSmallSpectrum380.graph fusedMap0515=true := by decide +kernel
theorem certified0515 : Certified (graph core0515) (root 7) 0 2 :=
  of_native_maps core0515 DegreeOneSmallSpectrum533.graph DegreeOneSmallSpectrum380.graph
    sourceMap0515 fusedMap0515 sourceMap0515_checked fusedMap0515_checked
    DegreeOneSmallComparisons.comparison0515
#print axioms sourceMap0515_checked
#print axioms fusedMap0515_checked
#print axioms certified0515
def sourceMap0515swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0515swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0515swap_checked : acceptsGraphIso
    (source (graph core0515) (root 7) 2 0) DegreeOneSmallSpectrum533.graph sourceMap0515swap=true := by decide +kernel
theorem fusedMap0515swap_checked : acceptsGraphIso
    (fused (graph core0515) (root 7) 2 0) DegreeOneSmallSpectrum380.graph fusedMap0515swap=true := by decide +kernel
theorem certified0515swap : Certified (graph core0515) (root 7) 2 0 :=
  of_native_maps core0515 DegreeOneSmallSpectrum533.graph DegreeOneSmallSpectrum380.graph
    sourceMap0515swap fusedMap0515swap sourceMap0515swap_checked fusedMap0515swap_checked
    DegreeOneSmallComparisons.comparison0515
#print axioms sourceMap0515swap_checked
#print axioms fusedMap0515swap_checked
#print axioms certified0515swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
