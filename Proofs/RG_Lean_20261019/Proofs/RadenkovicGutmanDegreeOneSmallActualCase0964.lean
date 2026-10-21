/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0964 : Family 8 := level8.get ⟨79,by decide⟩
def sourceMap0964 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0964 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (fusedLabel 8 0 1 v)
theorem sourceMap0964_checked : acceptsGraphIso
    (source (graph core0964) (root 8) 0 1) DegreeOneSmallSpectrum543.graph sourceMap0964=true := by decide +kernel
theorem fusedMap0964_checked : acceptsGraphIso
    (fused (graph core0964) (root 8) 0 1) DegreeOneSmallSpectrum584.graph fusedMap0964=true := by decide +kernel
theorem certified0964 : Certified (graph core0964) (root 8) 0 1 :=
  of_native_maps core0964 DegreeOneSmallSpectrum543.graph DegreeOneSmallSpectrum584.graph
    sourceMap0964 fusedMap0964 sourceMap0964_checked fusedMap0964_checked
    DegreeOneSmallComparisons.comparison0964
#print axioms sourceMap0964_checked
#print axioms fusedMap0964_checked
#print axioms certified0964
def sourceMap0964swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0964swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (fusedLabel 8 1 0 v)
theorem sourceMap0964swap_checked : acceptsGraphIso
    (source (graph core0964) (root 8) 1 0) DegreeOneSmallSpectrum543.graph sourceMap0964swap=true := by decide +kernel
theorem fusedMap0964swap_checked : acceptsGraphIso
    (fused (graph core0964) (root 8) 1 0) DegreeOneSmallSpectrum584.graph fusedMap0964swap=true := by decide +kernel
theorem certified0964swap : Certified (graph core0964) (root 8) 1 0 :=
  of_native_maps core0964 DegreeOneSmallSpectrum543.graph DegreeOneSmallSpectrum584.graph
    sourceMap0964swap fusedMap0964swap sourceMap0964swap_checked fusedMap0964swap_checked
    DegreeOneSmallComparisons.comparison0964
#print axioms sourceMap0964swap_checked
#print axioms fusedMap0964swap_checked
#print axioms certified0964swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
