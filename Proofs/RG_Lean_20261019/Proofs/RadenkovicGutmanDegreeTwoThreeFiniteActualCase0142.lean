/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0142 : Family 8 := level8.get ⟨223,by decide⟩
def sourceMap0142 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0142 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0142_checked : acceptsGraphIso
    (source (graph core0142) (root 8) 0 0) DegreeOneSmallSpectrum311.graph sourceMap0142=true := by decide +kernel
theorem fusedMap0142_checked : acceptsGraphIso
    (fused (graph core0142) (root 8) 0 0) DegreeOneSmallSpectrum310.graph fusedMap0142=true := by decide +kernel
theorem certified0142 : Certified (graph core0142) (root 8) 0 0 :=
  of_native_maps core0142 DegreeOneSmallSpectrum311.graph DegreeOneSmallSpectrum310.graph
    sourceMap0142 fusedMap0142 sourceMap0142_checked fusedMap0142_checked
    DegreeTwoThreeFiniteComparisons.comparison0142
#print axioms sourceMap0142_checked
#print axioms fusedMap0142_checked
#print axioms certified0142
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
