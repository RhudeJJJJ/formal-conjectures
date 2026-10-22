/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0835 : Family 10 := level10.get ⟨1292,by decide⟩
def sourceMap0835 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0835 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0835_checked : acceptsGraphIso
    (source (graph core0835) (root 10) 0 0) DegreeOneSmallSpectrum1651.graph sourceMap0835=true := by decide +kernel
theorem fusedMap0835_checked : acceptsGraphIso
    (fused (graph core0835) (root 10) 0 0) DegreeOneSmallSpectrum1634.graph fusedMap0835=true := by decide +kernel
theorem certified0835 : Certified (graph core0835) (root 10) 0 0 :=
  of_native_maps core0835 DegreeOneSmallSpectrum1651.graph DegreeOneSmallSpectrum1634.graph
    sourceMap0835 fusedMap0835 sourceMap0835_checked fusedMap0835_checked
    DegreeTwoThreeFiniteComparisons.comparison0835
#print axioms sourceMap0835_checked
#print axioms fusedMap0835_checked
#print axioms certified0835
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
