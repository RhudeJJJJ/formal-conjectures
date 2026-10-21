/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0332 : Family 6 := level6.get ⟨8,by decide⟩
def sourceMap0332 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0332 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0332_checked : acceptsGraphIso
    (source (graph core0332) (root 6) 0 2) DegreeOneSmallSpectrum187.graph sourceMap0332=true := by decide +kernel
theorem fusedMap0332_checked : acceptsGraphIso
    (fused (graph core0332) (root 6) 0 2) DegreeOneSmallSpectrum188.graph fusedMap0332=true := by decide +kernel
theorem certified0332 : Certified (graph core0332) (root 6) 0 2 :=
  of_native_maps core0332 DegreeOneSmallSpectrum187.graph DegreeOneSmallSpectrum188.graph
    sourceMap0332 fusedMap0332 sourceMap0332_checked fusedMap0332_checked
    DegreeOneSmallComparisons.comparison0332
#print axioms sourceMap0332_checked
#print axioms fusedMap0332_checked
#print axioms certified0332
def sourceMap0332swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0332swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0332swap_checked : acceptsGraphIso
    (source (graph core0332) (root 6) 2 0) DegreeOneSmallSpectrum187.graph sourceMap0332swap=true := by decide +kernel
theorem fusedMap0332swap_checked : acceptsGraphIso
    (fused (graph core0332) (root 6) 2 0) DegreeOneSmallSpectrum188.graph fusedMap0332swap=true := by decide +kernel
theorem certified0332swap : Certified (graph core0332) (root 6) 2 0 :=
  of_native_maps core0332 DegreeOneSmallSpectrum187.graph DegreeOneSmallSpectrum188.graph
    sourceMap0332swap fusedMap0332swap sourceMap0332swap_checked fusedMap0332swap_checked
    DegreeOneSmallComparisons.comparison0332
#print axioms sourceMap0332swap_checked
#print axioms fusedMap0332swap_checked
#print axioms certified0332swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
