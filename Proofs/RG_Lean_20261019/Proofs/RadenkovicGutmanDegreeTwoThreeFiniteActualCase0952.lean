/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0952 : Family 10 := level10.get ⟨1584,by decide⟩
def sourceMap0952 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0952 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0952_checked : acceptsGraphIso
    (source (graph core0952) (root 10) 0 0) DegreeTwoThreeSpectrum1699.graph sourceMap0952=true := by decide +kernel
theorem fusedMap0952_checked : acceptsGraphIso
    (fused (graph core0952) (root 10) 0 0) DegreeOneSmallSpectrum1640.graph fusedMap0952=true := by decide +kernel
theorem certified0952 : Certified (graph core0952) (root 10) 0 0 :=
  of_native_maps core0952 DegreeTwoThreeSpectrum1699.graph DegreeOneSmallSpectrum1640.graph
    sourceMap0952 fusedMap0952 sourceMap0952_checked fusedMap0952_checked
    DegreeTwoThreeFiniteComparisons.comparison0952
#print axioms sourceMap0952_checked
#print axioms fusedMap0952_checked
#print axioms certified0952
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
