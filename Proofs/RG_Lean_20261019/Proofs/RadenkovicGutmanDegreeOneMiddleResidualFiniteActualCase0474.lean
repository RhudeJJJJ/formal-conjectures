/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0474 : Family 9 := level9.get ⟨585,by decide⟩
def sourceMap0474 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0474 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0474_checked : acceptsGraphIso
    (source (graph core0474) (root 9) 2 2) DegreeOneMiddleResidualSpectrum918.graph sourceMap0474=true := by decide +kernel
theorem fusedMap0474_checked : acceptsGraphIso
    (fused (graph core0474) (root 9) 2 2) DegreeTwoThreeSpectrum4259.graph fusedMap0474=true := by decide +kernel
theorem certified0474 : Certified (graph core0474) (root 9) 2 2 :=
  of_native_maps core0474 DegreeOneMiddleResidualSpectrum918.graph DegreeTwoThreeSpectrum4259.graph
    sourceMap0474 fusedMap0474 sourceMap0474_checked fusedMap0474_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0474
#print axioms sourceMap0474_checked
#print axioms fusedMap0474_checked
#print axioms certified0474
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
