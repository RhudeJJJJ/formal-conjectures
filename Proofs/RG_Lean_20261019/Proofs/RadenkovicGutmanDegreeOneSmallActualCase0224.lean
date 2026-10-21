/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0224 : Family 5 := level5.get ⟨6,by decide⟩
def sourceMap0224 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap0224 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap0224_checked : acceptsGraphIso
    (source (graph core0224) (root 5) 0 5) DegreeOneSmallSpectrum873.graph sourceMap0224=true := by decide +kernel
theorem fusedMap0224_checked : acceptsGraphIso
    (fused (graph core0224) (root 5) 0 5) DegreeOneSmallSpectrum879.graph fusedMap0224=true := by decide +kernel
theorem certified0224 : Certified (graph core0224) (root 5) 0 5 :=
  of_native_maps core0224 DegreeOneSmallSpectrum873.graph DegreeOneSmallSpectrum879.graph
    sourceMap0224 fusedMap0224 sourceMap0224_checked fusedMap0224_checked
    DegreeOneSmallComparisons.comparison0224
#print axioms sourceMap0224_checked
#print axioms fusedMap0224_checked
#print axioms certified0224
def sourceMap0224swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,12,7] (sourceLabel 5 5 0 v)
def fusedMap0224swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap0224swap_checked : acceptsGraphIso
    (source (graph core0224) (root 5) 5 0) DegreeOneSmallSpectrum873.graph sourceMap0224swap=true := by decide +kernel
theorem fusedMap0224swap_checked : acceptsGraphIso
    (fused (graph core0224) (root 5) 5 0) DegreeOneSmallSpectrum879.graph fusedMap0224swap=true := by decide +kernel
theorem certified0224swap : Certified (graph core0224) (root 5) 5 0 :=
  of_native_maps core0224 DegreeOneSmallSpectrum873.graph DegreeOneSmallSpectrum879.graph
    sourceMap0224swap fusedMap0224swap sourceMap0224swap_checked fusedMap0224swap_checked
    DegreeOneSmallComparisons.comparison0224
#print axioms sourceMap0224swap_checked
#print axioms fusedMap0224swap_checked
#print axioms certified0224swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
