/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0146 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0146 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (sourceLabel 4 0 3 v)
def fusedMap0146 : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 0 3 v)
theorem sourceMap0146_checked : acceptsGraphIso
    (source (graph core0146) (root 4) 0 3) DegreeOneSmallSpectrum101.graph sourceMap0146=true := by decide +kernel
theorem fusedMap0146_checked : acceptsGraphIso
    (fused (graph core0146) (root 4) 0 3) DegreeOneSmallSpectrum074.graph fusedMap0146=true := by decide +kernel
theorem certified0146 : Certified (graph core0146) (root 4) 0 3 :=
  of_native_maps core0146 DegreeOneSmallSpectrum101.graph DegreeOneSmallSpectrum074.graph
    sourceMap0146 fusedMap0146 sourceMap0146_checked fusedMap0146_checked
    DegreeOneSmallComparisons.comparison0146
#print axioms sourceMap0146_checked
#print axioms fusedMap0146_checked
#print axioms certified0146
def sourceMap0146swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,7,8,9,6] (sourceLabel 4 3 0 v)
def fusedMap0146swap : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 3 0 v)
theorem sourceMap0146swap_checked : acceptsGraphIso
    (source (graph core0146) (root 4) 3 0) DegreeOneSmallSpectrum101.graph sourceMap0146swap=true := by decide +kernel
theorem fusedMap0146swap_checked : acceptsGraphIso
    (fused (graph core0146) (root 4) 3 0) DegreeOneSmallSpectrum074.graph fusedMap0146swap=true := by decide +kernel
theorem certified0146swap : Certified (graph core0146) (root 4) 3 0 :=
  of_native_maps core0146 DegreeOneSmallSpectrum101.graph DegreeOneSmallSpectrum074.graph
    sourceMap0146swap fusedMap0146swap sourceMap0146swap_checked fusedMap0146swap_checked
    DegreeOneSmallComparisons.comparison0146
#print axioms sourceMap0146swap_checked
#print axioms fusedMap0146swap_checked
#print axioms certified0146swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
