/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0487 : Family 10 := level10.get ⟨358,by decide⟩
def sourceMap0487 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0487 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0487_checked : acceptsGraphIso
    (source (graph core0487) (root 10) 0 0) DegreeOneSmallSpectrum1013.graph sourceMap0487=true := by decide +kernel
theorem fusedMap0487_checked : acceptsGraphIso
    (fused (graph core0487) (root 10) 0 0) DegreeOneSmallSpectrum1410.graph fusedMap0487=true := by decide +kernel
theorem certified0487 : Certified (graph core0487) (root 10) 0 0 :=
  of_native_maps core0487 DegreeOneSmallSpectrum1013.graph DegreeOneSmallSpectrum1410.graph
    sourceMap0487 fusedMap0487 sourceMap0487_checked fusedMap0487_checked
    DegreeTwoThreeFiniteComparisons.comparison0487
#print axioms sourceMap0487_checked
#print axioms fusedMap0487_checked
#print axioms certified0487
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
