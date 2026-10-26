/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3750 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap3750 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,7,8,9,6,2,3,4,5] (sourceLabel 5 1 1 v)
def fusedMap3750 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,9,5,6,7,8] (fusedLabel 5 1 1 v)
theorem sourceMap3750_checked : acceptsGraphIso
    (source (graph core3750) (root 5) 1 1) DegreeOneSmallSpectrum133.graph sourceMap3750=true := by decide +kernel
theorem fusedMap3750_checked : acceptsGraphIso
    (fused (graph core3750) (root 5) 1 1) DegreeOneSmallSpectrum091.graph fusedMap3750=true := by decide +kernel
theorem certified3750 : Certified (graph core3750) (root 5) 1 1 :=
  of_native_maps core3750 DegreeOneSmallSpectrum133.graph DegreeOneSmallSpectrum091.graph
    sourceMap3750 fusedMap3750 sourceMap3750_checked fusedMap3750_checked
    DegreeTwoThreeFiniteComparisons.comparison3750
#print axioms sourceMap3750_checked
#print axioms fusedMap3750_checked
#print axioms certified3750
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
