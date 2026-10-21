/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0179 : Family 5 := level5.get ⟨1,by decide⟩
def sourceMap0179 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,10,11,6,7,8,9] (sourceLabel 5 1 3 v)
def fusedMap0179 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 1 3 v)
theorem sourceMap0179_checked : acceptsGraphIso
    (source (graph core0179) (root 5) 1 3) DegreeOneSmallSpectrum498.graph sourceMap0179=true := by decide +kernel
theorem fusedMap0179_checked : acceptsGraphIso
    (fused (graph core0179) (root 5) 1 3) DegreeOneSmallSpectrum378.graph fusedMap0179=true := by decide +kernel
theorem certified0179 : Certified (graph core0179) (root 5) 1 3 :=
  of_native_maps core0179 DegreeOneSmallSpectrum498.graph DegreeOneSmallSpectrum378.graph
    sourceMap0179 fusedMap0179 sourceMap0179_checked fusedMap0179_checked
    DegreeOneSmallComparisons.comparison0179
#print axioms sourceMap0179_checked
#print axioms fusedMap0179_checked
#print axioms certified0179
def sourceMap0179swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 3 1 v)
def fusedMap0179swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 3 1 v)
theorem sourceMap0179swap_checked : acceptsGraphIso
    (source (graph core0179) (root 5) 3 1) DegreeOneSmallSpectrum498.graph sourceMap0179swap=true := by decide +kernel
theorem fusedMap0179swap_checked : acceptsGraphIso
    (fused (graph core0179) (root 5) 3 1) DegreeOneSmallSpectrum378.graph fusedMap0179swap=true := by decide +kernel
theorem certified0179swap : Certified (graph core0179) (root 5) 3 1 :=
  of_native_maps core0179 DegreeOneSmallSpectrum498.graph DegreeOneSmallSpectrum378.graph
    sourceMap0179swap fusedMap0179swap sourceMap0179swap_checked fusedMap0179swap_checked
    DegreeOneSmallComparisons.comparison0179
#print axioms sourceMap0179swap_checked
#print axioms fusedMap0179swap_checked
#print axioms certified0179swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
