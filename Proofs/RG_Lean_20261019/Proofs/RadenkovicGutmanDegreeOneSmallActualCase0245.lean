/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0245 : Family 5 := level5.get ⟨9,by decide⟩
def sourceMap0245 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,9,6,7,8] (sourceLabel 5 0 2 v)
def fusedMap0245 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap0245_checked : acceptsGraphIso
    (source (graph core0245) (root 5) 0 2) DegreeOneSmallSpectrum142.graph sourceMap0245=true := by decide +kernel
theorem fusedMap0245_checked : acceptsGraphIso
    (fused (graph core0245) (root 5) 0 2) DegreeOneSmallSpectrum082.graph fusedMap0245=true := by decide +kernel
theorem certified0245 : Certified (graph core0245) (root 5) 0 2 :=
  of_native_maps core0245 DegreeOneSmallSpectrum142.graph DegreeOneSmallSpectrum082.graph
    sourceMap0245 fusedMap0245 sourceMap0245_checked fusedMap0245_checked
    DegreeOneSmallComparisons.comparison0245
#print axioms sourceMap0245_checked
#print axioms fusedMap0245_checked
#print axioms certified0245
def sourceMap0245swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 5 2 0 v)
def fusedMap0245swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap0245swap_checked : acceptsGraphIso
    (source (graph core0245) (root 5) 2 0) DegreeOneSmallSpectrum142.graph sourceMap0245swap=true := by decide +kernel
theorem fusedMap0245swap_checked : acceptsGraphIso
    (fused (graph core0245) (root 5) 2 0) DegreeOneSmallSpectrum082.graph fusedMap0245swap=true := by decide +kernel
theorem certified0245swap : Certified (graph core0245) (root 5) 2 0 :=
  of_native_maps core0245 DegreeOneSmallSpectrum142.graph DegreeOneSmallSpectrum082.graph
    sourceMap0245swap fusedMap0245swap sourceMap0245swap_checked fusedMap0245swap_checked
    DegreeOneSmallComparisons.comparison0245
#print axioms sourceMap0245swap_checked
#print axioms fusedMap0245swap_checked
#print axioms certified0245swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
