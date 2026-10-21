/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0297 : Family 6 := level6.get ⟨3,by decide⟩
def sourceMap0297 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (sourceLabel 6 0 3 v)
def fusedMap0297 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0297_checked : acceptsGraphIso
    (source (graph core0297) (root 6) 0 3) DegreeOneSmallSpectrum391.graph sourceMap0297=true := by decide +kernel
theorem fusedMap0297_checked : acceptsGraphIso
    (fused (graph core0297) (root 6) 0 3) DegreeOneSmallSpectrum392.graph fusedMap0297=true := by decide +kernel
theorem certified0297 : Certified (graph core0297) (root 6) 0 3 :=
  of_native_maps core0297 DegreeOneSmallSpectrum391.graph DegreeOneSmallSpectrum392.graph
    sourceMap0297 fusedMap0297 sourceMap0297_checked fusedMap0297_checked
    DegreeOneSmallComparisons.comparison0297
#print axioms sourceMap0297_checked
#print axioms fusedMap0297_checked
#print axioms certified0297
def sourceMap0297swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 6 3 0 v)
def fusedMap0297swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0297swap_checked : acceptsGraphIso
    (source (graph core0297) (root 6) 3 0) DegreeOneSmallSpectrum391.graph sourceMap0297swap=true := by decide +kernel
theorem fusedMap0297swap_checked : acceptsGraphIso
    (fused (graph core0297) (root 6) 3 0) DegreeOneSmallSpectrum392.graph fusedMap0297swap=true := by decide +kernel
theorem certified0297swap : Certified (graph core0297) (root 6) 3 0 :=
  of_native_maps core0297 DegreeOneSmallSpectrum391.graph DegreeOneSmallSpectrum392.graph
    sourceMap0297swap fusedMap0297swap sourceMap0297swap_checked fusedMap0297swap_checked
    DegreeOneSmallComparisons.comparison0297
#print axioms sourceMap0297swap_checked
#print axioms fusedMap0297swap_checked
#print axioms certified0297swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
