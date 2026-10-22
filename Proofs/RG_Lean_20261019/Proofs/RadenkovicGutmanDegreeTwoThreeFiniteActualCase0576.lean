/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0576 : Family 10 := level10.get ⟨630,by decide⟩
def sourceMap0576 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0576 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0576_checked : acceptsGraphIso
    (source (graph core0576) (root 10) 0 0) DegreeOneSmallSpectrum1661.graph sourceMap0576=true := by decide +kernel
theorem fusedMap0576_checked : acceptsGraphIso
    (fused (graph core0576) (root 10) 0 0) DegreeOneSmallSpectrum1206.graph fusedMap0576=true := by decide +kernel
theorem certified0576 : Certified (graph core0576) (root 10) 0 0 :=
  of_native_maps core0576 DegreeOneSmallSpectrum1661.graph DegreeOneSmallSpectrum1206.graph
    sourceMap0576 fusedMap0576 sourceMap0576_checked fusedMap0576_checked
    DegreeTwoThreeFiniteComparisons.comparison0576
#print axioms sourceMap0576_checked
#print axioms fusedMap0576_checked
#print axioms certified0576
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
