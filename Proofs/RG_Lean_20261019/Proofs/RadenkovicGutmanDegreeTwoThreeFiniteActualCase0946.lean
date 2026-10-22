/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0946 : Family 10 := level10.get ⟨1571,by decide⟩
def sourceMap0946 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0946 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0946_checked : acceptsGraphIso
    (source (graph core0946) (root 10) 0 0) DegreeOneSmallSpectrum1614.graph sourceMap0946=true := by decide +kernel
theorem fusedMap0946_checked : acceptsGraphIso
    (fused (graph core0946) (root 10) 0 0) DegreeOneSmallSpectrum1613.graph fusedMap0946=true := by decide +kernel
theorem certified0946 : Certified (graph core0946) (root 10) 0 0 :=
  of_native_maps core0946 DegreeOneSmallSpectrum1614.graph DegreeOneSmallSpectrum1613.graph
    sourceMap0946 fusedMap0946 sourceMap0946_checked fusedMap0946_checked
    DegreeTwoThreeFiniteComparisons.comparison0946
#print axioms sourceMap0946_checked
#print axioms fusedMap0946_checked
#print axioms certified0946
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
