/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0780 : Family 8 := level8.get ⟨12,by decide⟩
def sourceMap0780 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (sourceLabel 8 0 1 v)
def fusedMap0780 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (fusedLabel 8 0 1 v)
theorem sourceMap0780_checked : acceptsGraphIso
    (source (graph core0780) (root 8) 0 1) DegreeOneSmallSpectrum489.graph sourceMap0780=true := by decide +kernel
theorem fusedMap0780_checked : acceptsGraphIso
    (fused (graph core0780) (root 8) 0 1) DegreeOneSmallSpectrum377.graph fusedMap0780=true := by decide +kernel
theorem certified0780 : Certified (graph core0780) (root 8) 0 1 :=
  of_native_maps core0780 DegreeOneSmallSpectrum489.graph DegreeOneSmallSpectrum377.graph
    sourceMap0780 fusedMap0780 sourceMap0780_checked fusedMap0780_checked
    DegreeOneSmallComparisons.comparison0780
#print axioms sourceMap0780_checked
#print axioms fusedMap0780_checked
#print axioms certified0780
def sourceMap0780swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (sourceLabel 8 1 0 v)
def fusedMap0780swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (fusedLabel 8 1 0 v)
theorem sourceMap0780swap_checked : acceptsGraphIso
    (source (graph core0780) (root 8) 1 0) DegreeOneSmallSpectrum489.graph sourceMap0780swap=true := by decide +kernel
theorem fusedMap0780swap_checked : acceptsGraphIso
    (fused (graph core0780) (root 8) 1 0) DegreeOneSmallSpectrum377.graph fusedMap0780swap=true := by decide +kernel
theorem certified0780swap : Certified (graph core0780) (root 8) 1 0 :=
  of_native_maps core0780 DegreeOneSmallSpectrum489.graph DegreeOneSmallSpectrum377.graph
    sourceMap0780swap fusedMap0780swap sourceMap0780swap_checked fusedMap0780swap_checked
    DegreeOneSmallComparisons.comparison0780
#print axioms sourceMap0780swap_checked
#print axioms fusedMap0780swap_checked
#print axioms certified0780swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
