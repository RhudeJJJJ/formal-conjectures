/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0212 : Family 5 := level5.get ⟨5,by decide⟩
def sourceMap0212 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap0212 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap0212_checked : acceptsGraphIso
    (source (graph core0212) (root 5) 0 5) DegreeOneSmallSpectrum864.graph sourceMap0212=true := by decide +kernel
theorem fusedMap0212_checked : acceptsGraphIso
    (fused (graph core0212) (root 5) 0 5) DegreeOneSmallSpectrum870.graph fusedMap0212=true := by decide +kernel
theorem certified0212 : Certified (graph core0212) (root 5) 0 5 :=
  of_native_maps core0212 DegreeOneSmallSpectrum864.graph DegreeOneSmallSpectrum870.graph
    sourceMap0212 fusedMap0212 sourceMap0212_checked fusedMap0212_checked
    DegreeOneSmallComparisons.comparison0212
#print axioms sourceMap0212_checked
#print axioms fusedMap0212_checked
#print axioms certified0212
def sourceMap0212swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,12,7] (sourceLabel 5 5 0 v)
def fusedMap0212swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap0212swap_checked : acceptsGraphIso
    (source (graph core0212) (root 5) 5 0) DegreeOneSmallSpectrum864.graph sourceMap0212swap=true := by decide +kernel
theorem fusedMap0212swap_checked : acceptsGraphIso
    (fused (graph core0212) (root 5) 5 0) DegreeOneSmallSpectrum870.graph fusedMap0212swap=true := by decide +kernel
theorem certified0212swap : Certified (graph core0212) (root 5) 5 0 :=
  of_native_maps core0212 DegreeOneSmallSpectrum864.graph DegreeOneSmallSpectrum870.graph
    sourceMap0212swap fusedMap0212swap sourceMap0212swap_checked fusedMap0212swap_checked
    DegreeOneSmallComparisons.comparison0212
#print axioms sourceMap0212swap_checked
#print axioms fusedMap0212swap_checked
#print axioms certified0212swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
