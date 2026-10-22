/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0493 : Family 10 := level10.get ⟨375,by decide⟩
def sourceMap0493 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0493 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0493_checked : acceptsGraphIso
    (source (graph core0493) (root 10) 0 0) DegreeOneSmallSpectrum1075.graph sourceMap0493=true := by decide +kernel
theorem fusedMap0493_checked : acceptsGraphIso
    (fused (graph core0493) (root 10) 0 0) DegreeOneSmallSpectrum1442.graph fusedMap0493=true := by decide +kernel
theorem certified0493 : Certified (graph core0493) (root 10) 0 0 :=
  of_native_maps core0493 DegreeOneSmallSpectrum1075.graph DegreeOneSmallSpectrum1442.graph
    sourceMap0493 fusedMap0493 sourceMap0493_checked fusedMap0493_checked
    DegreeTwoThreeFiniteComparisons.comparison0493
#print axioms sourceMap0493_checked
#print axioms fusedMap0493_checked
#print axioms certified0493
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
