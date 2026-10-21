/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0152 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0152 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (sourceLabel 4 1 3 v)
def fusedMap0152 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 1 3 v)
theorem sourceMap0152_checked : acceptsGraphIso
    (source (graph core0152) (root 4) 1 3) DegreeOneSmallSpectrum249.graph sourceMap0152=true := by decide +kernel
theorem fusedMap0152_checked : acceptsGraphIso
    (fused (graph core0152) (root 4) 1 3) DegreeOneSmallSpectrum175.graph fusedMap0152=true := by decide +kernel
theorem certified0152 : Certified (graph core0152) (root 4) 1 3 :=
  of_native_maps core0152 DegreeOneSmallSpectrum249.graph DegreeOneSmallSpectrum175.graph
    sourceMap0152 fusedMap0152 sourceMap0152_checked fusedMap0152_checked
    DegreeOneSmallComparisons.comparison0152
#print axioms sourceMap0152_checked
#print axioms fusedMap0152_checked
#print axioms certified0152
def sourceMap0152swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,8,9,10,6,7] (sourceLabel 4 3 1 v)
def fusedMap0152swap : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 3 1 v)
theorem sourceMap0152swap_checked : acceptsGraphIso
    (source (graph core0152) (root 4) 3 1) DegreeOneSmallSpectrum249.graph sourceMap0152swap=true := by decide +kernel
theorem fusedMap0152swap_checked : acceptsGraphIso
    (fused (graph core0152) (root 4) 3 1) DegreeOneSmallSpectrum175.graph fusedMap0152swap=true := by decide +kernel
theorem certified0152swap : Certified (graph core0152) (root 4) 3 1 :=
  of_native_maps core0152 DegreeOneSmallSpectrum249.graph DegreeOneSmallSpectrum175.graph
    sourceMap0152swap fusedMap0152swap sourceMap0152swap_checked fusedMap0152swap_checked
    DegreeOneSmallComparisons.comparison0152
#print axioms sourceMap0152swap_checked
#print axioms fusedMap0152swap_checked
#print axioms certified0152swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
