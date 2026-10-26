/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3752 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap3752 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,6,7,8,9,5,1,2,3,4] (sourceLabel 5 1 1 v)
def fusedMap3752 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap3752_checked : acceptsGraphIso
    (source (graph core3752) (root 5) 1 1) DegreeOneSmallSpectrum132.graph sourceMap3752=true := by decide +kernel
theorem fusedMap3752_checked : acceptsGraphIso
    (fused (graph core3752) (root 5) 1 1) DegreeOneSmallSpectrum083.graph fusedMap3752=true := by decide +kernel
theorem certified3752 : Certified (graph core3752) (root 5) 1 1 :=
  of_native_maps core3752 DegreeOneSmallSpectrum132.graph DegreeOneSmallSpectrum083.graph
    sourceMap3752 fusedMap3752 sourceMap3752_checked fusedMap3752_checked
    DegreeTwoThreeFiniteComparisons.comparison3752
#print axioms sourceMap3752_checked
#print axioms fusedMap3752_checked
#print axioms certified3752
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
