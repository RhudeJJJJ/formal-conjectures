/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0227 : Family 5 := level5.get ⟨6,by decide⟩
def sourceMap0227 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 1 3 v)
def fusedMap0227 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 1 3 v)
theorem sourceMap0227_checked : acceptsGraphIso
    (source (graph core0227) (root 5) 1 3) DegreeOneSmallSpectrum441.graph sourceMap0227=true := by decide +kernel
theorem fusedMap0227_checked : acceptsGraphIso
    (fused (graph core0227) (root 5) 1 3) DegreeOneSmallSpectrum371.graph fusedMap0227=true := by decide +kernel
theorem certified0227 : Certified (graph core0227) (root 5) 1 3 :=
  of_native_maps core0227 DegreeOneSmallSpectrum441.graph DegreeOneSmallSpectrum371.graph
    sourceMap0227 fusedMap0227 sourceMap0227_checked fusedMap0227_checked
    DegreeOneSmallComparisons.comparison0227
#print axioms sourceMap0227_checked
#print axioms fusedMap0227_checked
#print axioms certified0227
def sourceMap0227swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,6,7] (sourceLabel 5 3 1 v)
def fusedMap0227swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 3 1 v)
theorem sourceMap0227swap_checked : acceptsGraphIso
    (source (graph core0227) (root 5) 3 1) DegreeOneSmallSpectrum441.graph sourceMap0227swap=true := by decide +kernel
theorem fusedMap0227swap_checked : acceptsGraphIso
    (fused (graph core0227) (root 5) 3 1) DegreeOneSmallSpectrum371.graph fusedMap0227swap=true := by decide +kernel
theorem certified0227swap : Certified (graph core0227) (root 5) 3 1 :=
  of_native_maps core0227 DegreeOneSmallSpectrum441.graph DegreeOneSmallSpectrum371.graph
    sourceMap0227swap fusedMap0227swap sourceMap0227swap_checked fusedMap0227swap_checked
    DegreeOneSmallComparisons.comparison0227
#print axioms sourceMap0227swap_checked
#print axioms fusedMap0227swap_checked
#print axioms certified0227swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
