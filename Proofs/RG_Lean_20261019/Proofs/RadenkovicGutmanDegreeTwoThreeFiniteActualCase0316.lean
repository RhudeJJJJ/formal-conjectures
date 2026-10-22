/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0316 : Family 9 := level9.get ⟨474,by decide⟩
def sourceMap0316 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0316 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0316_checked : acceptsGraphIso
    (source (graph core0316) (root 9) 0 0) DegreeOneSmallSpectrum726.graph sourceMap0316=true := by decide +kernel
theorem fusedMap0316_checked : acceptsGraphIso
    (fused (graph core0316) (root 9) 0 0) DegreeOneSmallSpectrum706.graph fusedMap0316=true := by decide +kernel
theorem certified0316 : Certified (graph core0316) (root 9) 0 0 :=
  of_native_maps core0316 DegreeOneSmallSpectrum726.graph DegreeOneSmallSpectrum706.graph
    sourceMap0316 fusedMap0316 sourceMap0316_checked fusedMap0316_checked
    DegreeTwoThreeFiniteComparisons.comparison0316
#print axioms sourceMap0316_checked
#print axioms fusedMap0316_checked
#print axioms certified0316
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
