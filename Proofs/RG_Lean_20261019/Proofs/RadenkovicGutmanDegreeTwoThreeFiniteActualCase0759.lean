/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0759 : Family 10 := level10.get ⟨1112,by decide⟩
def sourceMap0759 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0759 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0759_checked : acceptsGraphIso
    (source (graph core0759) (root 10) 0 0) DegreeOneSmallSpectrum1751.graph sourceMap0759=true := by decide +kernel
theorem fusedMap0759_checked : acceptsGraphIso
    (fused (graph core0759) (root 10) 0 0) DegreeOneSmallSpectrum1749.graph fusedMap0759=true := by decide +kernel
theorem certified0759 : Certified (graph core0759) (root 10) 0 0 :=
  of_native_maps core0759 DegreeOneSmallSpectrum1751.graph DegreeOneSmallSpectrum1749.graph
    sourceMap0759 fusedMap0759 sourceMap0759_checked fusedMap0759_checked
    DegreeTwoThreeFiniteComparisons.comparison0759
#print axioms sourceMap0759_checked
#print axioms fusedMap0759_checked
#print axioms certified0759
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
