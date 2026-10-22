/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0811 : Family 10 := level10.get ⟨1229,by decide⟩
def sourceMap0811 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0811 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0811_checked : acceptsGraphIso
    (source (graph core0811) (root 10) 0 0) DegreeOneSmallSpectrum1262.graph sourceMap0811=true := by decide +kernel
theorem fusedMap0811_checked : acceptsGraphIso
    (fused (graph core0811) (root 10) 0 0) DegreeOneSmallSpectrum1261.graph fusedMap0811=true := by decide +kernel
theorem certified0811 : Certified (graph core0811) (root 10) 0 0 :=
  of_native_maps core0811 DegreeOneSmallSpectrum1262.graph DegreeOneSmallSpectrum1261.graph
    sourceMap0811 fusedMap0811 sourceMap0811_checked fusedMap0811_checked
    DegreeTwoThreeFiniteComparisons.comparison0811
#print axioms sourceMap0811_checked
#print axioms fusedMap0811_checked
#print axioms certified0811
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
