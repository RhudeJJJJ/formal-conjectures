/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0094 : Family 8 := level8.get ⟨111,by decide⟩
def sourceMap0094 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0094 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0094_checked : acceptsGraphIso
    (source (graph core0094) (root 8) 0 0) DegreeOneSmallSpectrum259.graph sourceMap0094=true := by decide +kernel
theorem fusedMap0094_checked : acceptsGraphIso
    (fused (graph core0094) (root 8) 0 0) DegreeOneSmallSpectrum280.graph fusedMap0094=true := by decide +kernel
theorem certified0094 : Certified (graph core0094) (root 8) 0 0 :=
  of_native_maps core0094 DegreeOneSmallSpectrum259.graph DegreeOneSmallSpectrum280.graph
    sourceMap0094 fusedMap0094 sourceMap0094_checked fusedMap0094_checked
    DegreeTwoThreeFiniteComparisons.comparison0094
#print axioms sourceMap0094_checked
#print axioms fusedMap0094_checked
#print axioms certified0094
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
