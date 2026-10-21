/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0946 : Family 8 := level8.get ⟨72,by decide⟩
def sourceMap0946 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0946 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0946_checked : acceptsGraphIso
    (source (graph core0946) (root 8) 1 1) DegreeOneSmallSpectrum1342.graph sourceMap0946=true := by decide +kernel
theorem fusedMap0946_checked : acceptsGraphIso
    (fused (graph core0946) (root 8) 1 1) DegreeOneSmallSpectrum947.graph fusedMap0946=true := by decide +kernel
theorem certified0946 : Certified (graph core0946) (root 8) 1 1 :=
  of_native_maps core0946 DegreeOneSmallSpectrum1342.graph DegreeOneSmallSpectrum947.graph
    sourceMap0946 fusedMap0946 sourceMap0946_checked fusedMap0946_checked
    DegreeOneSmallComparisons.comparison0946
#print axioms sourceMap0946_checked
#print axioms fusedMap0946_checked
#print axioms certified0946
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
