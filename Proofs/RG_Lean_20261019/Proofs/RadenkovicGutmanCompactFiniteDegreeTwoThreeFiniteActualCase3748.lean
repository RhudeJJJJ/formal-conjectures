/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3748 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap3748 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,8,4,5,6,7] (sourceLabel 4 1 1 v)
def fusedMap3748 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (fusedLabel 4 1 1 v)
theorem sourceMap3748_checked : acceptsGraphIso
    (source (graph core3748) (root 4) 1 1) DegreeOneSmallSpectrum071.graph sourceMap3748=true := by decide +kernel
theorem fusedMap3748_checked : acceptsGraphIso
    (fused (graph core3748) (root 4) 1 1) DegreeOneSmallSpectrum047.graph fusedMap3748=true := by decide +kernel
theorem certified3748 : Certified (graph core3748) (root 4) 1 1 :=
  of_native_maps core3748 DegreeOneSmallSpectrum071.graph DegreeOneSmallSpectrum047.graph
    sourceMap3748 fusedMap3748 sourceMap3748_checked fusedMap3748_checked
    DegreeTwoThreeFiniteComparisons.comparison3748
#print axioms sourceMap3748_checked
#print axioms fusedMap3748_checked
#print axioms certified3748
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
