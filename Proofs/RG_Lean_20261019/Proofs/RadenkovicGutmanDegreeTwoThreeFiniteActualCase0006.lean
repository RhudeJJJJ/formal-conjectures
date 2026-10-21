/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0006 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap0006 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![1,0,5,6,7,2,3,4] (sourceLabel 5 0 0 v)
def fusedMap0006 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![4,0,1,2,3,7,5,6] (fusedLabel 5 0 0 v)
theorem sourceMap0006_checked : acceptsGraphIso
    (source (graph core0006) (root 5) 0 0) DegreeOneSmallSpectrum029.graph sourceMap0006=true := by decide +kernel
theorem fusedMap0006_checked : acceptsGraphIso
    (fused (graph core0006) (root 5) 0 0) DegreeOneSmallSpectrum020.graph fusedMap0006=true := by decide +kernel
theorem certified0006 : Certified (graph core0006) (root 5) 0 0 :=
  of_native_maps core0006 DegreeOneSmallSpectrum029.graph DegreeOneSmallSpectrum020.graph
    sourceMap0006 fusedMap0006 sourceMap0006_checked fusedMap0006_checked
    DegreeTwoThreeFiniteComparisons.comparison0006
#print axioms sourceMap0006_checked
#print axioms fusedMap0006_checked
#print axioms certified0006
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
