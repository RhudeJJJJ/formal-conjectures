/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3753 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap3753 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,7,8,9,1,2,3,4,5,6] (sourceLabel 5 1 1 v)
def fusedMap3753 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap3753_checked : acceptsGraphIso
    (source (graph core3753) (root 5) 1 1) DegreeOneSmallSpectrum130.graph sourceMap3753=true := by decide +kernel
theorem fusedMap3753_checked : acceptsGraphIso
    (fused (graph core3753) (root 5) 1 1) DegreeOneSmallSpectrum087.graph fusedMap3753=true := by decide +kernel
theorem certified3753 : Certified (graph core3753) (root 5) 1 1 :=
  of_native_maps core3753 DegreeOneSmallSpectrum130.graph DegreeOneSmallSpectrum087.graph
    sourceMap3753 fusedMap3753 sourceMap3753_checked fusedMap3753_checked
    DegreeTwoThreeFiniteComparisons.comparison3753
#print axioms sourceMap3753_checked
#print axioms fusedMap3753_checked
#print axioms certified3753
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
