/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0593 : Family 7 := level7.get ⟨32,by decide⟩
def sourceMap0593 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0593 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0593_checked : acceptsGraphIso
    (source (graph core0593) (root 7) 0 2) DegreeOneSmallSpectrum445.graph sourceMap0593=true := by decide +kernel
theorem fusedMap0593_checked : acceptsGraphIso
    (fused (graph core0593) (root 7) 0 2) DegreeOneSmallSpectrum446.graph fusedMap0593=true := by decide +kernel
theorem certified0593 : Certified (graph core0593) (root 7) 0 2 :=
  of_native_maps core0593 DegreeOneSmallSpectrum445.graph DegreeOneSmallSpectrum446.graph
    sourceMap0593 fusedMap0593 sourceMap0593_checked fusedMap0593_checked
    DegreeOneSmallComparisons.comparison0593
#print axioms sourceMap0593_checked
#print axioms fusedMap0593_checked
#print axioms certified0593
def sourceMap0593swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0593swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0593swap_checked : acceptsGraphIso
    (source (graph core0593) (root 7) 2 0) DegreeOneSmallSpectrum445.graph sourceMap0593swap=true := by decide +kernel
theorem fusedMap0593swap_checked : acceptsGraphIso
    (fused (graph core0593) (root 7) 2 0) DegreeOneSmallSpectrum446.graph fusedMap0593swap=true := by decide +kernel
theorem certified0593swap : Certified (graph core0593) (root 7) 2 0 :=
  of_native_maps core0593 DegreeOneSmallSpectrum445.graph DegreeOneSmallSpectrum446.graph
    sourceMap0593swap fusedMap0593swap sourceMap0593swap_checked fusedMap0593swap_checked
    DegreeOneSmallComparisons.comparison0593
#print axioms sourceMap0593swap_checked
#print axioms fusedMap0593swap_checked
#print axioms certified0593swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
