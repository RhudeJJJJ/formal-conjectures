/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0283 : Family 9 := level9.get ⟨396,by decide⟩
def sourceMap0283 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,10,11,6,7,8,9] (sourceLabel 9 0 0 v)
def fusedMap0283 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,10,11,6,7,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap0283_checked : acceptsGraphIso
    (source (graph core0283) (root 9) 0 0) DegreeOneSmallSpectrum759.graph sourceMap0283=true := by decide +kernel
theorem fusedMap0283_checked : acceptsGraphIso
    (fused (graph core0283) (root 9) 0 0) DegreeOneSmallSpectrum754.graph fusedMap0283=true := by decide +kernel
theorem certified0283 : Certified (graph core0283) (root 9) 0 0 :=
  of_native_maps core0283 DegreeOneSmallSpectrum759.graph DegreeOneSmallSpectrum754.graph
    sourceMap0283 fusedMap0283 sourceMap0283_checked fusedMap0283_checked
    DegreeTwoThreeFiniteComparisons.comparison0283
#print axioms sourceMap0283_checked
#print axioms fusedMap0283_checked
#print axioms certified0283
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
