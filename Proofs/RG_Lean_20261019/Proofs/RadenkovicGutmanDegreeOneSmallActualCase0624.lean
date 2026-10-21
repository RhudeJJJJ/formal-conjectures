/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0624 : Family 7 := level7.get ⟨42,by decide⟩
def sourceMap0624 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0624 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0624_checked : acceptsGraphIso
    (source (graph core0624) (root 7) 0 3) DegreeOneSmallSpectrum1364.graph sourceMap0624=true := by decide +kernel
theorem fusedMap0624_checked : acceptsGraphIso
    (fused (graph core0624) (root 7) 0 3) DegreeOneSmallSpectrum916.graph fusedMap0624=true := by decide +kernel
theorem certified0624 : Certified (graph core0624) (root 7) 0 3 :=
  of_native_maps core0624 DegreeOneSmallSpectrum1364.graph DegreeOneSmallSpectrum916.graph
    sourceMap0624 fusedMap0624 sourceMap0624_checked fusedMap0624_checked
    DegreeOneSmallComparisons.comparison0624
#print axioms sourceMap0624_checked
#print axioms fusedMap0624_checked
#print axioms certified0624
def sourceMap0624swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0624swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0624swap_checked : acceptsGraphIso
    (source (graph core0624) (root 7) 3 0) DegreeOneSmallSpectrum1364.graph sourceMap0624swap=true := by decide +kernel
theorem fusedMap0624swap_checked : acceptsGraphIso
    (fused (graph core0624) (root 7) 3 0) DegreeOneSmallSpectrum916.graph fusedMap0624swap=true := by decide +kernel
theorem certified0624swap : Certified (graph core0624) (root 7) 3 0 :=
  of_native_maps core0624 DegreeOneSmallSpectrum1364.graph DegreeOneSmallSpectrum916.graph
    sourceMap0624swap fusedMap0624swap sourceMap0624swap_checked fusedMap0624swap_checked
    DegreeOneSmallComparisons.comparison0624
#print axioms sourceMap0624swap_checked
#print axioms fusedMap0624swap_checked
#print axioms certified0624swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
