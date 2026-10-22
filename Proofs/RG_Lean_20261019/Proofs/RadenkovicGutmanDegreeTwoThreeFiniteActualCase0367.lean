/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0367 : Family 9 := level9.get ⟨596,by decide⟩
def sourceMap0367 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0367 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0367_checked : acceptsGraphIso
    (source (graph core0367) (root 9) 0 0) DegreeOneSmallSpectrum708.graph sourceMap0367=true := by decide +kernel
theorem fusedMap0367_checked : acceptsGraphIso
    (fused (graph core0367) (root 9) 0 0) DegreeOneSmallSpectrum707.graph fusedMap0367=true := by decide +kernel
theorem certified0367 : Certified (graph core0367) (root 9) 0 0 :=
  of_native_maps core0367 DegreeOneSmallSpectrum708.graph DegreeOneSmallSpectrum707.graph
    sourceMap0367 fusedMap0367 sourceMap0367_checked fusedMap0367_checked
    DegreeTwoThreeFiniteComparisons.comparison0367
#print axioms sourceMap0367_checked
#print axioms fusedMap0367_checked
#print axioms certified0367
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
