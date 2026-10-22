/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0481 : Family 10 := level10.get ⟨339,by decide⟩
def sourceMap0481 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0481 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0481_checked : acceptsGraphIso
    (source (graph core0481) (root 10) 0 0) DegreeOneSmallSpectrum1032.graph sourceMap0481=true := by decide +kernel
theorem fusedMap0481_checked : acceptsGraphIso
    (fused (graph core0481) (root 10) 0 0) DegreeOneSmallSpectrum1425.graph fusedMap0481=true := by decide +kernel
theorem certified0481 : Certified (graph core0481) (root 10) 0 0 :=
  of_native_maps core0481 DegreeOneSmallSpectrum1032.graph DegreeOneSmallSpectrum1425.graph
    sourceMap0481 fusedMap0481 sourceMap0481_checked fusedMap0481_checked
    DegreeTwoThreeFiniteComparisons.comparison0481
#print axioms sourceMap0481_checked
#print axioms fusedMap0481_checked
#print axioms certified0481
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
