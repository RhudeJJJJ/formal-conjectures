/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0753 : Family 8 := level8.get ⟨4,by decide⟩
def sourceMap0753 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 8 0 2 v)
def fusedMap0753 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0753_checked : acceptsGraphIso
    (source (graph core0753) (root 8) 0 2) DegreeOneSmallSpectrum965.graph sourceMap0753=true := by decide +kernel
theorem fusedMap0753_checked : acceptsGraphIso
    (fused (graph core0753) (root 8) 0 2) DegreeOneSmallSpectrum859.graph fusedMap0753=true := by decide +kernel
theorem certified0753 : Certified (graph core0753) (root 8) 0 2 :=
  of_native_maps core0753 DegreeOneSmallSpectrum965.graph DegreeOneSmallSpectrum859.graph
    sourceMap0753 fusedMap0753 sourceMap0753_checked fusedMap0753_checked
    DegreeOneSmallComparisons.comparison0753
#print axioms sourceMap0753_checked
#print axioms fusedMap0753_checked
#print axioms certified0753
def sourceMap0753swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 2 0 v)
def fusedMap0753swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0753swap_checked : acceptsGraphIso
    (source (graph core0753) (root 8) 2 0) DegreeOneSmallSpectrum965.graph sourceMap0753swap=true := by decide +kernel
theorem fusedMap0753swap_checked : acceptsGraphIso
    (fused (graph core0753) (root 8) 2 0) DegreeOneSmallSpectrum859.graph fusedMap0753swap=true := by decide +kernel
theorem certified0753swap : Certified (graph core0753) (root 8) 2 0 :=
  of_native_maps core0753 DegreeOneSmallSpectrum965.graph DegreeOneSmallSpectrum859.graph
    sourceMap0753swap fusedMap0753swap sourceMap0753swap_checked fusedMap0753swap_checked
    DegreeOneSmallComparisons.comparison0753
#print axioms sourceMap0753swap_checked
#print axioms fusedMap0753swap_checked
#print axioms certified0753swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
