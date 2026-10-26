/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3746 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap3746 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,1,2,7,3,4,5,6] (sourceLabel 3 1 1 v)
def fusedMap3746 : (Vertices 3 ⊕ Fin 4) → Fin 8 :=
  fun v => ![1,2,3,4,0,5,6,7] (fusedLabel 3 1 1 v)
theorem sourceMap3746_checked : acceptsGraphIso
    (source (graph core3746) (root 3) 1 1) DegreeTwoThreeSpectrum030.graph sourceMap3746=true := by decide +kernel
theorem fusedMap3746_checked : acceptsGraphIso
    (fused (graph core3746) (root 3) 1 1) DegreeOneSmallSpectrum025.graph fusedMap3746=true := by decide +kernel
theorem certified3746 : Certified (graph core3746) (root 3) 1 1 :=
  of_native_maps core3746 DegreeTwoThreeSpectrum030.graph DegreeOneSmallSpectrum025.graph
    sourceMap3746 fusedMap3746 sourceMap3746_checked fusedMap3746_checked
    DegreeTwoThreeFiniteComparisons.comparison3746
#print axioms sourceMap3746_checked
#print axioms fusedMap3746_checked
#print axioms certified3746
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
