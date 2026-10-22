/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0972 : Family 10 := level10.get ⟨1632,by decide⟩
def sourceMap0972 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0972 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0972_checked : acceptsGraphIso
    (source (graph core0972) (root 10) 0 0) DegreeOneSmallSpectrum1741.graph sourceMap0972=true := by decide +kernel
theorem fusedMap0972_checked : acceptsGraphIso
    (fused (graph core0972) (root 10) 0 0) DegreeOneSmallSpectrum1740.graph fusedMap0972=true := by decide +kernel
theorem certified0972 : Certified (graph core0972) (root 10) 0 0 :=
  of_native_maps core0972 DegreeOneSmallSpectrum1741.graph DegreeOneSmallSpectrum1740.graph
    sourceMap0972 fusedMap0972 sourceMap0972_checked fusedMap0972_checked
    DegreeTwoThreeFiniteComparisons.comparison0972
#print axioms sourceMap0972_checked
#print axioms fusedMap0972_checked
#print axioms certified0972
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
