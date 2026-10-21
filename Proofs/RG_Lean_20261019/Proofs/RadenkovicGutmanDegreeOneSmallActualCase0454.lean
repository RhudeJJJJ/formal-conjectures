/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0454 : Family 7 := level7.get ⟨1,by decide⟩
def sourceMap0454 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0454 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0454_checked : acceptsGraphIso
    (source (graph core0454) (root 7) 0 1) DegreeOneSmallSpectrum193.graph sourceMap0454=true := by decide +kernel
theorem fusedMap0454_checked : acceptsGraphIso
    (fused (graph core0454) (root 7) 0 1) DegreeOneSmallSpectrum164.graph fusedMap0454=true := by decide +kernel
theorem certified0454 : Certified (graph core0454) (root 7) 0 1 :=
  of_native_maps core0454 DegreeOneSmallSpectrum193.graph DegreeOneSmallSpectrum164.graph
    sourceMap0454 fusedMap0454 sourceMap0454_checked fusedMap0454_checked
    DegreeOneSmallComparisons.comparison0454
#print axioms sourceMap0454_checked
#print axioms fusedMap0454_checked
#print axioms certified0454
def sourceMap0454swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0454swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0454swap_checked : acceptsGraphIso
    (source (graph core0454) (root 7) 1 0) DegreeOneSmallSpectrum193.graph sourceMap0454swap=true := by decide +kernel
theorem fusedMap0454swap_checked : acceptsGraphIso
    (fused (graph core0454) (root 7) 1 0) DegreeOneSmallSpectrum164.graph fusedMap0454swap=true := by decide +kernel
theorem certified0454swap : Certified (graph core0454) (root 7) 1 0 :=
  of_native_maps core0454 DegreeOneSmallSpectrum193.graph DegreeOneSmallSpectrum164.graph
    sourceMap0454swap fusedMap0454swap sourceMap0454swap_checked fusedMap0454swap_checked
    DegreeOneSmallComparisons.comparison0454
#print axioms sourceMap0454swap_checked
#print axioms fusedMap0454swap_checked
#print axioms certified0454swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
