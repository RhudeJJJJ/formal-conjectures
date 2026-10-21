/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0896 : Family 8 := level8.get ⟨54,by decide⟩
def sourceMap0896 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0896 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0896_checked : acceptsGraphIso
    (source (graph core0896) (root 8) 0 1) DegreeOneSmallSpectrum508.graph sourceMap0896=true := by decide +kernel
theorem fusedMap0896_checked : acceptsGraphIso
    (fused (graph core0896) (root 8) 0 1) DegreeOneSmallSpectrum510.graph fusedMap0896=true := by decide +kernel
theorem certified0896 : Certified (graph core0896) (root 8) 0 1 :=
  of_native_maps core0896 DegreeOneSmallSpectrum508.graph DegreeOneSmallSpectrum510.graph
    sourceMap0896 fusedMap0896 sourceMap0896_checked fusedMap0896_checked
    DegreeOneSmallComparisons.comparison0896
#print axioms sourceMap0896_checked
#print axioms fusedMap0896_checked
#print axioms certified0896
def sourceMap0896swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0896swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0896swap_checked : acceptsGraphIso
    (source (graph core0896) (root 8) 1 0) DegreeOneSmallSpectrum508.graph sourceMap0896swap=true := by decide +kernel
theorem fusedMap0896swap_checked : acceptsGraphIso
    (fused (graph core0896) (root 8) 1 0) DegreeOneSmallSpectrum510.graph fusedMap0896swap=true := by decide +kernel
theorem certified0896swap : Certified (graph core0896) (root 8) 1 0 :=
  of_native_maps core0896 DegreeOneSmallSpectrum508.graph DegreeOneSmallSpectrum510.graph
    sourceMap0896swap fusedMap0896swap sourceMap0896swap_checked fusedMap0896swap_checked
    DegreeOneSmallComparisons.comparison0896
#print axioms sourceMap0896swap_checked
#print axioms fusedMap0896swap_checked
#print axioms certified0896swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
