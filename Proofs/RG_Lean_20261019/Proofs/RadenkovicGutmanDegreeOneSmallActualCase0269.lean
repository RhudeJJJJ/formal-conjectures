/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0269 : Family 6 := level6.get ⟨0,by decide⟩
def sourceMap0269 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,2,3,4] (sourceLabel 6 0 2 v)
def fusedMap0269 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (fusedLabel 6 0 2 v)
theorem sourceMap0269_checked : acceptsGraphIso
    (source (graph core0269) (root 6) 0 2) DegreeOneSmallSpectrum166.graph sourceMap0269=true := by decide +kernel
theorem fusedMap0269_checked : acceptsGraphIso
    (fused (graph core0269) (root 6) 0 2) DegreeOneSmallSpectrum168.graph fusedMap0269=true := by decide +kernel
theorem certified0269 : Certified (graph core0269) (root 6) 0 2 :=
  of_native_maps core0269 DegreeOneSmallSpectrum166.graph DegreeOneSmallSpectrum168.graph
    sourceMap0269 fusedMap0269 sourceMap0269_checked fusedMap0269_checked
    DegreeOneSmallComparisons.comparison0269
#print axioms sourceMap0269_checked
#print axioms fusedMap0269_checked
#print axioms certified0269
def sourceMap0269swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 6 2 0 v)
def fusedMap0269swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (fusedLabel 6 2 0 v)
theorem sourceMap0269swap_checked : acceptsGraphIso
    (source (graph core0269) (root 6) 2 0) DegreeOneSmallSpectrum166.graph sourceMap0269swap=true := by decide +kernel
theorem fusedMap0269swap_checked : acceptsGraphIso
    (fused (graph core0269) (root 6) 2 0) DegreeOneSmallSpectrum168.graph fusedMap0269swap=true := by decide +kernel
theorem certified0269swap : Certified (graph core0269) (root 6) 2 0 :=
  of_native_maps core0269 DegreeOneSmallSpectrum166.graph DegreeOneSmallSpectrum168.graph
    sourceMap0269swap fusedMap0269swap sourceMap0269swap_checked fusedMap0269swap_checked
    DegreeOneSmallComparisons.comparison0269
#print axioms sourceMap0269swap_checked
#print axioms fusedMap0269swap_checked
#print axioms certified0269swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
