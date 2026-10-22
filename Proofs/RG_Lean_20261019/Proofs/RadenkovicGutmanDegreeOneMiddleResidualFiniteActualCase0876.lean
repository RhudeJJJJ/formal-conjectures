/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0876 : Family 10 := level10.get ⟨622,by decide⟩
def sourceMap0876 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0876 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0876_checked : acceptsGraphIso
    (source (graph core0876) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2116.graph sourceMap0876=true := by decide +kernel
theorem fusedMap0876_checked : acceptsGraphIso
    (fused (graph core0876) (root 10) 2 2) DegreeTwoThreeSpectrum5313.graph fusedMap0876=true := by decide +kernel
theorem certified0876 : Certified (graph core0876) (root 10) 2 2 :=
  of_native_maps core0876 DegreeOneMiddleResidualSpectrum2116.graph DegreeTwoThreeSpectrum5313.graph
    sourceMap0876 fusedMap0876 sourceMap0876_checked fusedMap0876_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0876
#print axioms sourceMap0876_checked
#print axioms fusedMap0876_checked
#print axioms certified0876
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
