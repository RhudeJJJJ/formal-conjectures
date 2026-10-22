/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0905 : Family 10 := level10.get ⟨1459,by decide⟩
def sourceMap0905 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,10,11,12,5,6,7,8,9,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0905 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0905_checked : acceptsGraphIso
    (source (graph core0905) (root 10) 0 0) DegreeOneSmallSpectrum1638.graph sourceMap0905=true := by decide +kernel
theorem fusedMap0905_checked : acceptsGraphIso
    (fused (graph core0905) (root 10) 0 0) DegreeOneSmallSpectrum1971.graph fusedMap0905=true := by decide +kernel
theorem certified0905 : Certified (graph core0905) (root 10) 0 0 :=
  of_native_maps core0905 DegreeOneSmallSpectrum1638.graph DegreeOneSmallSpectrum1971.graph
    sourceMap0905 fusedMap0905 sourceMap0905_checked fusedMap0905_checked
    DegreeTwoThreeFiniteComparisons.comparison0905
#print axioms sourceMap0905_checked
#print axioms fusedMap0905_checked
#print axioms certified0905
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
