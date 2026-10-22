/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0285 : Family 9 := level9.get ⟨400,by decide⟩
def sourceMap0285 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,10,11,6,7,8,9] (sourceLabel 9 0 0 v)
def fusedMap0285 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,10,11,6,7,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap0285_checked : acceptsGraphIso
    (source (graph core0285) (root 9) 0 0) DegreeOneSmallSpectrum760.graph sourceMap0285=true := by decide +kernel
theorem fusedMap0285_checked : acceptsGraphIso
    (fused (graph core0285) (root 9) 0 0) DegreeOneSmallSpectrum755.graph fusedMap0285=true := by decide +kernel
theorem certified0285 : Certified (graph core0285) (root 9) 0 0 :=
  of_native_maps core0285 DegreeOneSmallSpectrum760.graph DegreeOneSmallSpectrum755.graph
    sourceMap0285 fusedMap0285 sourceMap0285_checked fusedMap0285_checked
    DegreeTwoThreeFiniteComparisons.comparison0285
#print axioms sourceMap0285_checked
#print axioms fusedMap0285_checked
#print axioms certified0285
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
