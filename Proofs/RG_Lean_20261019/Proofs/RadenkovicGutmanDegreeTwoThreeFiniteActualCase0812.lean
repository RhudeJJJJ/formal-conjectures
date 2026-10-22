/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0812 : Family 10 := level10.get ⟨1233,by decide⟩
def sourceMap0812 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,2,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0812 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,2,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0812_checked : acceptsGraphIso
    (source (graph core0812) (root 10) 0 0) DegreeOneSmallSpectrum1574.graph sourceMap0812=true := by decide +kernel
theorem fusedMap0812_checked : acceptsGraphIso
    (fused (graph core0812) (root 10) 0 0) DegreeOneSmallSpectrum1565.graph fusedMap0812=true := by decide +kernel
theorem certified0812 : Certified (graph core0812) (root 10) 0 0 :=
  of_native_maps core0812 DegreeOneSmallSpectrum1574.graph DegreeOneSmallSpectrum1565.graph
    sourceMap0812 fusedMap0812 sourceMap0812_checked fusedMap0812_checked
    DegreeTwoThreeFiniteComparisons.comparison0812
#print axioms sourceMap0812_checked
#print axioms fusedMap0812_checked
#print axioms certified0812
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
