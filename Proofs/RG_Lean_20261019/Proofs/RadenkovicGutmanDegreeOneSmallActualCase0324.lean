/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0324 : Family 6 := level6.get ⟨7,by decide⟩
def sourceMap0324 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (sourceLabel 6 0 3 v)
def fusedMap0324 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0324_checked : acceptsGraphIso
    (source (graph core0324) (root 6) 0 3) DegreeOneSmallSpectrum457.graph sourceMap0324=true := by decide +kernel
theorem fusedMap0324_checked : acceptsGraphIso
    (fused (graph core0324) (root 6) 0 3) DegreeOneSmallSpectrum371.graph fusedMap0324=true := by decide +kernel
theorem certified0324 : Certified (graph core0324) (root 6) 0 3 :=
  of_native_maps core0324 DegreeOneSmallSpectrum457.graph DegreeOneSmallSpectrum371.graph
    sourceMap0324 fusedMap0324 sourceMap0324_checked fusedMap0324_checked
    DegreeOneSmallComparisons.comparison0324
#print axioms sourceMap0324_checked
#print axioms fusedMap0324_checked
#print axioms certified0324
def sourceMap0324swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 3 0 v)
def fusedMap0324swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0324swap_checked : acceptsGraphIso
    (source (graph core0324) (root 6) 3 0) DegreeOneSmallSpectrum457.graph sourceMap0324swap=true := by decide +kernel
theorem fusedMap0324swap_checked : acceptsGraphIso
    (fused (graph core0324) (root 6) 3 0) DegreeOneSmallSpectrum371.graph fusedMap0324swap=true := by decide +kernel
theorem certified0324swap : Certified (graph core0324) (root 6) 3 0 :=
  of_native_maps core0324 DegreeOneSmallSpectrum457.graph DegreeOneSmallSpectrum371.graph
    sourceMap0324swap fusedMap0324swap sourceMap0324swap_checked fusedMap0324swap_checked
    DegreeOneSmallComparisons.comparison0324
#print axioms sourceMap0324swap_checked
#print axioms fusedMap0324swap_checked
#print axioms certified0324swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
