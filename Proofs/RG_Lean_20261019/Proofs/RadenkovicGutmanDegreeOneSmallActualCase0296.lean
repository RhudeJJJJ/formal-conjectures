/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0296 : Family 6 := level6.get ⟨3,by decide⟩
def sourceMap0296 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,2,3,4] (sourceLabel 6 0 2 v)
def fusedMap0296 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0296_checked : acceptsGraphIso
    (source (graph core0296) (root 6) 0 2) DegreeOneSmallSpectrum226.graph sourceMap0296=true := by decide +kernel
theorem fusedMap0296_checked : acceptsGraphIso
    (fused (graph core0296) (root 6) 0 2) DegreeOneSmallSpectrum166.graph fusedMap0296=true := by decide +kernel
theorem certified0296 : Certified (graph core0296) (root 6) 0 2 :=
  of_native_maps core0296 DegreeOneSmallSpectrum226.graph DegreeOneSmallSpectrum166.graph
    sourceMap0296 fusedMap0296 sourceMap0296_checked fusedMap0296_checked
    DegreeOneSmallComparisons.comparison0296
#print axioms sourceMap0296_checked
#print axioms fusedMap0296_checked
#print axioms certified0296
def sourceMap0296swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 6 2 0 v)
def fusedMap0296swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0296swap_checked : acceptsGraphIso
    (source (graph core0296) (root 6) 2 0) DegreeOneSmallSpectrum226.graph sourceMap0296swap=true := by decide +kernel
theorem fusedMap0296swap_checked : acceptsGraphIso
    (fused (graph core0296) (root 6) 2 0) DegreeOneSmallSpectrum166.graph fusedMap0296swap=true := by decide +kernel
theorem certified0296swap : Certified (graph core0296) (root 6) 2 0 :=
  of_native_maps core0296 DegreeOneSmallSpectrum226.graph DegreeOneSmallSpectrum166.graph
    sourceMap0296swap fusedMap0296swap sourceMap0296swap_checked fusedMap0296swap_checked
    DegreeOneSmallComparisons.comparison0296
#print axioms sourceMap0296swap_checked
#print axioms fusedMap0296swap_checked
#print axioms certified0296swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
