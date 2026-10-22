/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0521 : Family 10 := level10.get ⟨461,by decide⟩
def sourceMap0521 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0521 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0521_checked : acceptsGraphIso
    (source (graph core0521) (root 10) 0 0) DegreeOneSmallSpectrum1380.graph sourceMap0521=true := by decide +kernel
theorem fusedMap0521_checked : acceptsGraphIso
    (fused (graph core0521) (root 10) 0 0) DegreeOneSmallSpectrum1331.graph fusedMap0521=true := by decide +kernel
theorem certified0521 : Certified (graph core0521) (root 10) 0 0 :=
  of_native_maps core0521 DegreeOneSmallSpectrum1380.graph DegreeOneSmallSpectrum1331.graph
    sourceMap0521 fusedMap0521 sourceMap0521_checked fusedMap0521_checked
    DegreeTwoThreeFiniteComparisons.comparison0521
#print axioms sourceMap0521_checked
#print axioms fusedMap0521_checked
#print axioms certified0521
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
