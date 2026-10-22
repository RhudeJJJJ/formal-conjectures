/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3745 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap3745 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 2) → Fin 7 :=
  fun v => ![0,5,6,1,2,3,4] (sourceLabel 2 1 1 v)
def fusedMap3745 : (Vertices 2 ⊕ Fin 4) → Fin 7 :=
  fun v => ![1,2,3,0,4,5,6] (fusedLabel 2 1 1 v)
theorem sourceMap3745_checked : acceptsGraphIso
    (source (graph core3745) (root 2) 1 1) DegreeTwoThreeSpectrum013.graph sourceMap3745=true := by decide +kernel
theorem fusedMap3745_checked : acceptsGraphIso
    (fused (graph core3745) (root 2) 1 1) DegreeOneSmallSpectrum008.graph fusedMap3745=true := by decide +kernel
theorem certified3745 : Certified (graph core3745) (root 2) 1 1 :=
  of_native_maps core3745 DegreeTwoThreeSpectrum013.graph DegreeOneSmallSpectrum008.graph
    sourceMap3745 fusedMap3745 sourceMap3745_checked fusedMap3745_checked
    DegreeTwoThreeFiniteComparisons.comparison3745
#print axioms sourceMap3745_checked
#print axioms fusedMap3745_checked
#print axioms certified3745
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
