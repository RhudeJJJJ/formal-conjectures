/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0153 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0153 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 4 1 4 v)
def fusedMap0153 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 1 4 v)
theorem sourceMap0153_checked : acceptsGraphIso
    (source (graph core0153) (root 4) 1 4) DegreeOneSmallSpectrum405.graph sourceMap0153=true := by decide +kernel
theorem fusedMap0153_checked : acceptsGraphIso
    (fused (graph core0153) (root 4) 1 4) DegreeOneSmallSpectrum370.graph fusedMap0153=true := by decide +kernel
theorem certified0153 : Certified (graph core0153) (root 4) 1 4 :=
  of_native_maps core0153 DegreeOneSmallSpectrum405.graph DegreeOneSmallSpectrum370.graph
    sourceMap0153 fusedMap0153 sourceMap0153_checked fusedMap0153_checked
    DegreeOneSmallComparisons.comparison0153
#print axioms sourceMap0153_checked
#print axioms fusedMap0153_checked
#print axioms certified0153
def sourceMap0153swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,2,3,4,5,0,8,9,10,11,6,7] (sourceLabel 4 4 1 v)
def fusedMap0153swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 4 1 v)
theorem sourceMap0153swap_checked : acceptsGraphIso
    (source (graph core0153) (root 4) 4 1) DegreeOneSmallSpectrum405.graph sourceMap0153swap=true := by decide +kernel
theorem fusedMap0153swap_checked : acceptsGraphIso
    (fused (graph core0153) (root 4) 4 1) DegreeOneSmallSpectrum370.graph fusedMap0153swap=true := by decide +kernel
theorem certified0153swap : Certified (graph core0153) (root 4) 4 1 :=
  of_native_maps core0153 DegreeOneSmallSpectrum405.graph DegreeOneSmallSpectrum370.graph
    sourceMap0153swap fusedMap0153swap sourceMap0153swap_checked fusedMap0153swap_checked
    DegreeOneSmallComparisons.comparison0153
#print axioms sourceMap0153swap_checked
#print axioms fusedMap0153swap_checked
#print axioms certified0153swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
