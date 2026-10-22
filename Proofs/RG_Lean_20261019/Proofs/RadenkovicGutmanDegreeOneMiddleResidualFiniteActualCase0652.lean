/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0652 : Family 10 := level10.get ⟨229,by decide⟩
def sourceMap0652 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0652 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0652_checked : acceptsGraphIso
    (source (graph core0652) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1645.graph sourceMap0652=true := by decide +kernel
theorem fusedMap0652_checked : acceptsGraphIso
    (fused (graph core0652) (root 10) 2 2) DegreeTwoThreeSpectrum5279.graph fusedMap0652=true := by decide +kernel
theorem certified0652 : Certified (graph core0652) (root 10) 2 2 :=
  of_native_maps core0652 DegreeOneMiddleResidualSpectrum1645.graph DegreeTwoThreeSpectrum5279.graph
    sourceMap0652 fusedMap0652 sourceMap0652_checked fusedMap0652_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0652
#print axioms sourceMap0652_checked
#print axioms fusedMap0652_checked
#print axioms certified0652
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
