/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0358 : Family 6 := level6.get ⟨12,by decide⟩
def sourceMap0358 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,4,2,3] (sourceLabel 6 0 1 v)
def fusedMap0358 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0358_checked : acceptsGraphIso
    (source (graph core0358) (root 6) 0 1) DegreeOneSmallSpectrum143.graph sourceMap0358=true := by decide +kernel
theorem fusedMap0358_checked : acceptsGraphIso
    (fused (graph core0358) (root 6) 0 1) DegreeOneSmallSpectrum083.graph fusedMap0358=true := by decide +kernel
theorem certified0358 : Certified (graph core0358) (root 6) 0 1 :=
  of_native_maps core0358 DegreeOneSmallSpectrum143.graph DegreeOneSmallSpectrum083.graph
    sourceMap0358 fusedMap0358 sourceMap0358_checked fusedMap0358_checked
    DegreeOneSmallComparisons.comparison0358
#print axioms sourceMap0358_checked
#print axioms fusedMap0358_checked
#print axioms certified0358
def sourceMap0358swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (sourceLabel 6 1 0 v)
def fusedMap0358swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0358swap_checked : acceptsGraphIso
    (source (graph core0358) (root 6) 1 0) DegreeOneSmallSpectrum143.graph sourceMap0358swap=true := by decide +kernel
theorem fusedMap0358swap_checked : acceptsGraphIso
    (fused (graph core0358) (root 6) 1 0) DegreeOneSmallSpectrum083.graph fusedMap0358swap=true := by decide +kernel
theorem certified0358swap : Certified (graph core0358) (root 6) 1 0 :=
  of_native_maps core0358 DegreeOneSmallSpectrum143.graph DegreeOneSmallSpectrum083.graph
    sourceMap0358swap fusedMap0358swap sourceMap0358swap_checked fusedMap0358swap_checked
    DegreeOneSmallComparisons.comparison0358
#print axioms sourceMap0358swap_checked
#print axioms fusedMap0358swap_checked
#print axioms certified0358swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
