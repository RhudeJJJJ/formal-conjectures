/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0691 : Family 10 := level10.get ⟨293,by decide⟩
def sourceMap0691 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0691 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0691_checked : acceptsGraphIso
    (source (graph core0691) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1739.graph sourceMap0691=true := by decide +kernel
theorem fusedMap0691_checked : acceptsGraphIso
    (fused (graph core0691) (root 10) 2 2) DegreeTwoThreeSpectrum5456.graph fusedMap0691=true := by decide +kernel
theorem certified0691 : Certified (graph core0691) (root 10) 2 2 :=
  of_native_maps core0691 DegreeOneMiddleResidualSpectrum1739.graph DegreeTwoThreeSpectrum5456.graph
    sourceMap0691 fusedMap0691 sourceMap0691_checked fusedMap0691_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0691
#print axioms sourceMap0691_checked
#print axioms fusedMap0691_checked
#print axioms certified0691
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
