/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0683 : Family 7 := level7.get ⟨65,by decide⟩
def sourceMap0683 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0683 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0683_checked : acceptsGraphIso
    (source (graph core0683) (root 7) 0 2) DegreeOneSmallSpectrum640.graph sourceMap0683=true := by decide +kernel
theorem fusedMap0683_checked : acceptsGraphIso
    (fused (graph core0683) (root 7) 0 2) DegreeOneSmallSpectrum405.graph fusedMap0683=true := by decide +kernel
theorem certified0683 : Certified (graph core0683) (root 7) 0 2 :=
  of_native_maps core0683 DegreeOneSmallSpectrum640.graph DegreeOneSmallSpectrum405.graph
    sourceMap0683 fusedMap0683 sourceMap0683_checked fusedMap0683_checked
    DegreeOneSmallComparisons.comparison0683
#print axioms sourceMap0683_checked
#print axioms fusedMap0683_checked
#print axioms certified0683
def sourceMap0683swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0683swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0683swap_checked : acceptsGraphIso
    (source (graph core0683) (root 7) 2 0) DegreeOneSmallSpectrum640.graph sourceMap0683swap=true := by decide +kernel
theorem fusedMap0683swap_checked : acceptsGraphIso
    (fused (graph core0683) (root 7) 2 0) DegreeOneSmallSpectrum405.graph fusedMap0683swap=true := by decide +kernel
theorem certified0683swap : Certified (graph core0683) (root 7) 2 0 :=
  of_native_maps core0683 DegreeOneSmallSpectrum640.graph DegreeOneSmallSpectrum405.graph
    sourceMap0683swap fusedMap0683swap sourceMap0683swap_checked fusedMap0683swap_checked
    DegreeOneSmallComparisons.comparison0683
#print axioms sourceMap0683swap_checked
#print axioms fusedMap0683swap_checked
#print axioms certified0683swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
