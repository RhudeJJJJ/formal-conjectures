/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0852 : Family 10 := level10.get ⟨1336,by decide⟩
def sourceMap0852 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0852 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0852_checked : acceptsGraphIso
    (source (graph core0852) (root 10) 0 0) DegreeOneSmallSpectrum1393.graph sourceMap0852=true := by decide +kernel
theorem fusedMap0852_checked : acceptsGraphIso
    (fused (graph core0852) (root 10) 0 0) DegreeOneSmallSpectrum1392.graph fusedMap0852=true := by decide +kernel
theorem certified0852 : Certified (graph core0852) (root 10) 0 0 :=
  of_native_maps core0852 DegreeOneSmallSpectrum1393.graph DegreeOneSmallSpectrum1392.graph
    sourceMap0852 fusedMap0852 sourceMap0852_checked fusedMap0852_checked
    DegreeTwoThreeFiniteComparisons.comparison0852
#print axioms sourceMap0852_checked
#print axioms fusedMap0852_checked
#print axioms certified0852
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
