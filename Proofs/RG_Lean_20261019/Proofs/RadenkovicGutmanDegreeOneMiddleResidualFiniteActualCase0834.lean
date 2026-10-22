/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0834 : Family 10 := level10.get ⟨547,by decide⟩
def sourceMap0834 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0834 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0834_checked : acceptsGraphIso
    (source (graph core0834) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2033.graph sourceMap0834=true := by decide +kernel
theorem fusedMap0834_checked : acceptsGraphIso
    (fused (graph core0834) (root 10) 2 2) DegreeTwoThreeSpectrum5201.graph fusedMap0834=true := by decide +kernel
theorem certified0834 : Certified (graph core0834) (root 10) 2 2 :=
  of_native_maps core0834 DegreeOneMiddleResidualSpectrum2033.graph DegreeTwoThreeSpectrum5201.graph
    sourceMap0834 fusedMap0834 sourceMap0834_checked fusedMap0834_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0834
#print axioms sourceMap0834_checked
#print axioms fusedMap0834_checked
#print axioms certified0834
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
