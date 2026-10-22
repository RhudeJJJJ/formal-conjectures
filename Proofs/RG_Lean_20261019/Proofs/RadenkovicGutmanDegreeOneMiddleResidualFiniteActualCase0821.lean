/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0821 : Family 10 := level10.get ⟨525,by decide⟩
def sourceMap0821 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0821 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0821_checked : acceptsGraphIso
    (source (graph core0821) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2011.graph sourceMap0821=true := by decide +kernel
theorem fusedMap0821_checked : acceptsGraphIso
    (fused (graph core0821) (root 10) 2 2) DegreeTwoThreeSpectrum5169.graph fusedMap0821=true := by decide +kernel
theorem certified0821 : Certified (graph core0821) (root 10) 2 2 :=
  of_native_maps core0821 DegreeOneMiddleResidualSpectrum2011.graph DegreeTwoThreeSpectrum5169.graph
    sourceMap0821 fusedMap0821 sourceMap0821_checked fusedMap0821_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0821
#print axioms sourceMap0821_checked
#print axioms fusedMap0821_checked
#print axioms certified0821
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
