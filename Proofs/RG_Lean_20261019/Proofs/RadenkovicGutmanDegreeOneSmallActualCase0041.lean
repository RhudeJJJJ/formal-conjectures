/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0041 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0041 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (sourceLabel 2 1 3 v)
def fusedMap0041 : (Vertices 2 ⊕ Fin 6) → Fin 9 :=
  fun v => ![2,3,4,1,0,5,6,7,8] (fusedLabel 2 1 3 v)
theorem sourceMap0041_checked : acceptsGraphIso
    (source (graph core0041) (root 2) 1 3) DegreeOneSmallSpectrum055.graph sourceMap0041=true := by decide +kernel
theorem fusedMap0041_checked : acceptsGraphIso
    (fused (graph core0041) (root 2) 1 3) DegreeOneSmallSpectrum037.graph fusedMap0041=true := by decide +kernel
theorem certified0041 : Certified (graph core0041) (root 2) 1 3 :=
  of_native_maps core0041 DegreeOneSmallSpectrum055.graph DegreeOneSmallSpectrum037.graph
    sourceMap0041 fusedMap0041 sourceMap0041_checked fusedMap0041_checked
    DegreeOneSmallComparisons.comparison0041
#print axioms sourceMap0041_checked
#print axioms fusedMap0041_checked
#print axioms certified0041
def sourceMap0041swap : (Vertices 2 ⊕ Fin 4 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,2,3,0,6,7,8,4,5] (sourceLabel 2 3 1 v)
def fusedMap0041swap : (Vertices 2 ⊕ Fin 6) → Fin 9 :=
  fun v => ![2,3,4,1,0,5,6,7,8] (fusedLabel 2 3 1 v)
theorem sourceMap0041swap_checked : acceptsGraphIso
    (source (graph core0041) (root 2) 3 1) DegreeOneSmallSpectrum055.graph sourceMap0041swap=true := by decide +kernel
theorem fusedMap0041swap_checked : acceptsGraphIso
    (fused (graph core0041) (root 2) 3 1) DegreeOneSmallSpectrum037.graph fusedMap0041swap=true := by decide +kernel
theorem certified0041swap : Certified (graph core0041) (root 2) 3 1 :=
  of_native_maps core0041 DegreeOneSmallSpectrum055.graph DegreeOneSmallSpectrum037.graph
    sourceMap0041swap fusedMap0041swap sourceMap0041swap_checked fusedMap0041swap_checked
    DegreeOneSmallComparisons.comparison0041
#print axioms sourceMap0041swap_checked
#print axioms fusedMap0041swap_checked
#print axioms certified0041swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
