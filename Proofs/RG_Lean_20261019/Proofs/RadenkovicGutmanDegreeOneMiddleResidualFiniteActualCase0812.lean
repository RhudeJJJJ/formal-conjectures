/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0812 : Family 10 := level10.get ⟨511,by decide⟩
def sourceMap0812 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0812 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0812_checked : acceptsGraphIso
    (source (graph core0812) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1987.graph sourceMap0812=true := by decide +kernel
theorem fusedMap0812_checked : acceptsGraphIso
    (fused (graph core0812) (root 10) 2 2) DegreeTwoThreeSpectrum5150.graph fusedMap0812=true := by decide +kernel
theorem certified0812 : Certified (graph core0812) (root 10) 2 2 :=
  of_native_maps core0812 DegreeOneMiddleResidualSpectrum1987.graph DegreeTwoThreeSpectrum5150.graph
    sourceMap0812 fusedMap0812 sourceMap0812_checked fusedMap0812_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0812
#print axioms sourceMap0812_checked
#print axioms fusedMap0812_checked
#print axioms certified0812
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
