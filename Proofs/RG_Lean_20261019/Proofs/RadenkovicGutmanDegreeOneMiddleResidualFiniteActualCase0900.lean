/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0900 : Family 10 := level10.get ⟨684,by decide⟩
def sourceMap0900 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0900 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0900_checked : acceptsGraphIso
    (source (graph core0900) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2148.graph sourceMap0900=true := by decide +kernel
theorem fusedMap0900_checked : acceptsGraphIso
    (fused (graph core0900) (root 10) 2 2) DegreeTwoThreeSpectrum5421.graph fusedMap0900=true := by decide +kernel
theorem certified0900 : Certified (graph core0900) (root 10) 2 2 :=
  of_native_maps core0900 DegreeOneMiddleResidualSpectrum2148.graph DegreeTwoThreeSpectrum5421.graph
    sourceMap0900 fusedMap0900 sourceMap0900_checked fusedMap0900_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0900
#print axioms sourceMap0900_checked
#print axioms fusedMap0900_checked
#print axioms certified0900
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
