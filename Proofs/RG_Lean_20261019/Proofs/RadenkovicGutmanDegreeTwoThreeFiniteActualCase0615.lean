/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0615 : Family 10 := level10.get ⟨736,by decide⟩
def sourceMap0615 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0615 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0615_checked : acceptsGraphIso
    (source (graph core0615) (root 10) 0 0) DegreeTwoThreeSpectrum1137.graph sourceMap0615=true := by decide +kernel
theorem fusedMap0615_checked : acceptsGraphIso
    (fused (graph core0615) (root 10) 0 0) DegreeOneSmallSpectrum1333.graph fusedMap0615=true := by decide +kernel
theorem certified0615 : Certified (graph core0615) (root 10) 0 0 :=
  of_native_maps core0615 DegreeTwoThreeSpectrum1137.graph DegreeOneSmallSpectrum1333.graph
    sourceMap0615 fusedMap0615 sourceMap0615_checked fusedMap0615_checked
    DegreeTwoThreeFiniteComparisons.comparison0615
#print axioms sourceMap0615_checked
#print axioms fusedMap0615_checked
#print axioms certified0615
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
