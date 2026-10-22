/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0924 : Family 10 := level10.get ⟨727,by decide⟩
def sourceMap0924 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0924 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0924_checked : acceptsGraphIso
    (source (graph core0924) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2191.graph sourceMap0924=true := by decide +kernel
theorem fusedMap0924_checked : acceptsGraphIso
    (fused (graph core0924) (root 10) 2 2) DegreeTwoThreeSpectrum5483.graph fusedMap0924=true := by decide +kernel
theorem certified0924 : Certified (graph core0924) (root 10) 2 2 :=
  of_native_maps core0924 DegreeOneMiddleResidualSpectrum2191.graph DegreeTwoThreeSpectrum5483.graph
    sourceMap0924 fusedMap0924 sourceMap0924_checked fusedMap0924_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0924
#print axioms sourceMap0924_checked
#print axioms fusedMap0924_checked
#print axioms certified0924
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
