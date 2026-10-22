/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0678 : Family 10 := level10.get ⟨268,by decide⟩
def sourceMap0678 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0678 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0678_checked : acceptsGraphIso
    (source (graph core0678) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1695.graph sourceMap0678=true := by decide +kernel
theorem fusedMap0678_checked : acceptsGraphIso
    (fused (graph core0678) (root 10) 2 2) DegreeTwoThreeSpectrum5389.graph fusedMap0678=true := by decide +kernel
theorem certified0678 : Certified (graph core0678) (root 10) 2 2 :=
  of_native_maps core0678 DegreeOneMiddleResidualSpectrum1695.graph DegreeTwoThreeSpectrum5389.graph
    sourceMap0678 fusedMap0678 sourceMap0678_checked fusedMap0678_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0678
#print axioms sourceMap0678_checked
#print axioms fusedMap0678_checked
#print axioms certified0678
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
