/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0295 : Family 6 := level6.get ⟨3,by decide⟩
def sourceMap0295 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,4,2,3] (sourceLabel 6 0 1 v)
def fusedMap0295 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0295_checked : acceptsGraphIso
    (source (graph core0295) (root 6) 0 1) DegreeOneSmallSpectrum085.graph sourceMap0295=true := by decide +kernel
theorem fusedMap0295_checked : acceptsGraphIso
    (fused (graph core0295) (root 6) 0 1) DegreeOneSmallSpectrum090.graph fusedMap0295=true := by decide +kernel
theorem certified0295 : Certified (graph core0295) (root 6) 0 1 :=
  of_native_maps core0295 DegreeOneSmallSpectrum085.graph DegreeOneSmallSpectrum090.graph
    sourceMap0295 fusedMap0295 sourceMap0295_checked fusedMap0295_checked
    DegreeOneSmallComparisons.comparison0295
#print axioms sourceMap0295_checked
#print axioms fusedMap0295_checked
#print axioms certified0295
def sourceMap0295swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (sourceLabel 6 1 0 v)
def fusedMap0295swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0295swap_checked : acceptsGraphIso
    (source (graph core0295) (root 6) 1 0) DegreeOneSmallSpectrum085.graph sourceMap0295swap=true := by decide +kernel
theorem fusedMap0295swap_checked : acceptsGraphIso
    (fused (graph core0295) (root 6) 1 0) DegreeOneSmallSpectrum090.graph fusedMap0295swap=true := by decide +kernel
theorem certified0295swap : Certified (graph core0295) (root 6) 1 0 :=
  of_native_maps core0295 DegreeOneSmallSpectrum085.graph DegreeOneSmallSpectrum090.graph
    sourceMap0295swap fusedMap0295swap sourceMap0295swap_checked fusedMap0295swap_checked
    DegreeOneSmallComparisons.comparison0295
#print axioms sourceMap0295swap_checked
#print axioms fusedMap0295swap_checked
#print axioms certified0295swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
