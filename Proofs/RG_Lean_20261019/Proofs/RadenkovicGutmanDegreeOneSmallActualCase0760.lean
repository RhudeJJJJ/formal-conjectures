/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0760 : Family 8 := level8.get ⟨6,by decide⟩
def sourceMap0760 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0760 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (fusedLabel 8 0 1 v)
theorem sourceMap0760_checked : acceptsGraphIso
    (source (graph core0760) (root 8) 0 1) DegreeOneSmallSpectrum381.graph sourceMap0760=true := by decide +kernel
theorem fusedMap0760_checked : acceptsGraphIso
    (fused (graph core0760) (root 8) 0 1) DegreeOneSmallSpectrum396.graph fusedMap0760=true := by decide +kernel
theorem certified0760 : Certified (graph core0760) (root 8) 0 1 :=
  of_native_maps core0760 DegreeOneSmallSpectrum381.graph DegreeOneSmallSpectrum396.graph
    sourceMap0760 fusedMap0760 sourceMap0760_checked fusedMap0760_checked
    DegreeOneSmallComparisons.comparison0760
#print axioms sourceMap0760_checked
#print axioms fusedMap0760_checked
#print axioms certified0760
def sourceMap0760swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0760swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (fusedLabel 8 1 0 v)
theorem sourceMap0760swap_checked : acceptsGraphIso
    (source (graph core0760) (root 8) 1 0) DegreeOneSmallSpectrum381.graph sourceMap0760swap=true := by decide +kernel
theorem fusedMap0760swap_checked : acceptsGraphIso
    (fused (graph core0760) (root 8) 1 0) DegreeOneSmallSpectrum396.graph fusedMap0760swap=true := by decide +kernel
theorem certified0760swap : Certified (graph core0760) (root 8) 1 0 :=
  of_native_maps core0760 DegreeOneSmallSpectrum381.graph DegreeOneSmallSpectrum396.graph
    sourceMap0760swap fusedMap0760swap sourceMap0760swap_checked fusedMap0760swap_checked
    DegreeOneSmallComparisons.comparison0760
#print axioms sourceMap0760swap_checked
#print axioms fusedMap0760swap_checked
#print axioms certified0760swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
