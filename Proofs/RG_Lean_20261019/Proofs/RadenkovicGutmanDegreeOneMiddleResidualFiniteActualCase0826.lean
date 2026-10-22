/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0826 : Family 10 := level10.get ⟨534,by decide⟩
def sourceMap0826 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0826 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0826_checked : acceptsGraphIso
    (source (graph core0826) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2020.graph sourceMap0826=true := by decide +kernel
theorem fusedMap0826_checked : acceptsGraphIso
    (fused (graph core0826) (root 10) 2 2) DegreeTwoThreeSpectrum5183.graph fusedMap0826=true := by decide +kernel
theorem certified0826 : Certified (graph core0826) (root 10) 2 2 :=
  of_native_maps core0826 DegreeOneMiddleResidualSpectrum2020.graph DegreeTwoThreeSpectrum5183.graph
    sourceMap0826 fusedMap0826 sourceMap0826_checked fusedMap0826_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0826
#print axioms sourceMap0826_checked
#print axioms fusedMap0826_checked
#print axioms certified0826
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
