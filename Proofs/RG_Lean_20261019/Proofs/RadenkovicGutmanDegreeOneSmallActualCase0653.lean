/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0653 : Family 7 := level7.get ⟨51,by decide⟩
def sourceMap0653 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0653 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0653_checked : acceptsGraphIso
    (source (graph core0653) (root 7) 0 2) DegreeOneSmallSpectrum566.graph sourceMap0653=true := by decide +kernel
theorem fusedMap0653_checked : acceptsGraphIso
    (fused (graph core0653) (root 7) 0 2) DegreeOneSmallSpectrum567.graph fusedMap0653=true := by decide +kernel
theorem certified0653 : Certified (graph core0653) (root 7) 0 2 :=
  of_native_maps core0653 DegreeOneSmallSpectrum566.graph DegreeOneSmallSpectrum567.graph
    sourceMap0653 fusedMap0653 sourceMap0653_checked fusedMap0653_checked
    DegreeOneSmallComparisons.comparison0653
#print axioms sourceMap0653_checked
#print axioms fusedMap0653_checked
#print axioms certified0653
def sourceMap0653swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0653swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0653swap_checked : acceptsGraphIso
    (source (graph core0653) (root 7) 2 0) DegreeOneSmallSpectrum566.graph sourceMap0653swap=true := by decide +kernel
theorem fusedMap0653swap_checked : acceptsGraphIso
    (fused (graph core0653) (root 7) 2 0) DegreeOneSmallSpectrum567.graph fusedMap0653swap=true := by decide +kernel
theorem certified0653swap : Certified (graph core0653) (root 7) 2 0 :=
  of_native_maps core0653 DegreeOneSmallSpectrum566.graph DegreeOneSmallSpectrum567.graph
    sourceMap0653swap fusedMap0653swap sourceMap0653swap_checked fusedMap0653swap_checked
    DegreeOneSmallComparisons.comparison0653
#print axioms sourceMap0653swap_checked
#print axioms fusedMap0653swap_checked
#print axioms certified0653swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
