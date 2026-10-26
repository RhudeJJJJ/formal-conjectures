/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3747 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap3747 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,6,7,8,5,1,2,3,4] (sourceLabel 4 1 1 v)
def fusedMap3747 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 4 1 1 v)
theorem sourceMap3747_checked : acceptsGraphIso
    (source (graph core3747) (root 4) 1 1) DegreeOneSmallSpectrum053.graph sourceMap3747=true := by decide +kernel
theorem fusedMap3747_checked : acceptsGraphIso
    (fused (graph core3747) (root 4) 1 1) DegreeOneSmallSpectrum036.graph fusedMap3747=true := by decide +kernel
theorem certified3747 : Certified (graph core3747) (root 4) 1 1 :=
  of_native_maps core3747 DegreeOneSmallSpectrum053.graph DegreeOneSmallSpectrum036.graph
    sourceMap3747 fusedMap3747 sourceMap3747_checked fusedMap3747_checked
    DegreeTwoThreeFiniteComparisons.comparison3747
#print axioms sourceMap3747_checked
#print axioms fusedMap3747_checked
#print axioms certified3747
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
