/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0638 : Family 10 := level10.get ⟨804,by decide⟩
def sourceMap0638 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,5,0,1,2,3,4,6,7,8,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0638 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0638_checked : acceptsGraphIso
    (source (graph core0638) (root 10) 0 0) DegreeOneSmallSpectrum1440.graph sourceMap0638=true := by decide +kernel
theorem fusedMap0638_checked : acceptsGraphIso
    (fused (graph core0638) (root 10) 0 0) DegreeOneSmallSpectrum1396.graph fusedMap0638=true := by decide +kernel
theorem certified0638 : Certified (graph core0638) (root 10) 0 0 :=
  of_native_maps core0638 DegreeOneSmallSpectrum1440.graph DegreeOneSmallSpectrum1396.graph
    sourceMap0638 fusedMap0638 sourceMap0638_checked fusedMap0638_checked
    DegreeTwoThreeFiniteComparisons.comparison0638
#print axioms sourceMap0638_checked
#print axioms fusedMap0638_checked
#print axioms certified0638
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
