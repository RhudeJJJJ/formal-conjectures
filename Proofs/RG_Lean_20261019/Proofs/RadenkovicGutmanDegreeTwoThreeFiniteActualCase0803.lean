/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0803 : Family 10 := level10.get ⟨1214,by decide⟩
def sourceMap0803 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0803 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0803_checked : acceptsGraphIso
    (source (graph core0803) (root 10) 0 0) DegreeOneSmallSpectrum1236.graph sourceMap0803=true := by decide +kernel
theorem fusedMap0803_checked : acceptsGraphIso
    (fused (graph core0803) (root 10) 0 0) DegreeOneSmallSpectrum1235.graph fusedMap0803=true := by decide +kernel
theorem certified0803 : Certified (graph core0803) (root 10) 0 0 :=
  of_native_maps core0803 DegreeOneSmallSpectrum1236.graph DegreeOneSmallSpectrum1235.graph
    sourceMap0803 fusedMap0803 sourceMap0803_checked fusedMap0803_checked
    DegreeTwoThreeFiniteComparisons.comparison0803
#print axioms sourceMap0803_checked
#print axioms fusedMap0803_checked
#print axioms certified0803
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
