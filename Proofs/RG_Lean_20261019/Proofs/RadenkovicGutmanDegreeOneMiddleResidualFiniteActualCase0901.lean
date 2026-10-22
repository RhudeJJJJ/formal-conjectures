/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0901 : Family 10 := level10.get ⟨685,by decide⟩
def sourceMap0901 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0901 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0901_checked : acceptsGraphIso
    (source (graph core0901) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2149.graph sourceMap0901=true := by decide +kernel
theorem fusedMap0901_checked : acceptsGraphIso
    (fused (graph core0901) (root 10) 2 2) DegreeTwoThreeSpectrum5422.graph fusedMap0901=true := by decide +kernel
theorem certified0901 : Certified (graph core0901) (root 10) 2 2 :=
  of_native_maps core0901 DegreeOneMiddleResidualSpectrum2149.graph DegreeTwoThreeSpectrum5422.graph
    sourceMap0901 fusedMap0901 sourceMap0901_checked fusedMap0901_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0901
#print axioms sourceMap0901_checked
#print axioms fusedMap0901_checked
#print axioms certified0901
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
