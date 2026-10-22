/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0638 : Family 10 := level10.get ⟨210,by decide⟩
def sourceMap0638 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0638 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0638_checked : acceptsGraphIso
    (source (graph core0638) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1589.graph sourceMap0638=true := by decide +kernel
theorem fusedMap0638_checked : acceptsGraphIso
    (fused (graph core0638) (root 10) 2 2) DegreeTwoThreeSpectrum5216.graph fusedMap0638=true := by decide +kernel
theorem certified0638 : Certified (graph core0638) (root 10) 2 2 :=
  of_native_maps core0638 DegreeOneMiddleResidualSpectrum1589.graph DegreeTwoThreeSpectrum5216.graph
    sourceMap0638 fusedMap0638 sourceMap0638_checked fusedMap0638_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0638
#print axioms sourceMap0638_checked
#print axioms fusedMap0638_checked
#print axioms certified0638
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
