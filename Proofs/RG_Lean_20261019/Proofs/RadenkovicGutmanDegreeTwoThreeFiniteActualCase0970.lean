/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0970 : Family 10 := level10.get ⟨1628,by decide⟩
def sourceMap0970 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0970 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0970_checked : acceptsGraphIso
    (source (graph core0970) (root 10) 0 0) DegreeOneSmallSpectrum1731.graph sourceMap0970=true := by decide +kernel
theorem fusedMap0970_checked : acceptsGraphIso
    (fused (graph core0970) (root 10) 0 0) DegreeOneSmallSpectrum1730.graph fusedMap0970=true := by decide +kernel
theorem certified0970 : Certified (graph core0970) (root 10) 0 0 :=
  of_native_maps core0970 DegreeOneSmallSpectrum1731.graph DegreeOneSmallSpectrum1730.graph
    sourceMap0970 fusedMap0970 sourceMap0970_checked fusedMap0970_checked
    DegreeTwoThreeFiniteComparisons.comparison0970
#print axioms sourceMap0970_checked
#print axioms fusedMap0970_checked
#print axioms certified0970
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
