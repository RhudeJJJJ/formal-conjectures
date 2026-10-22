/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0279 : Family 9 := level9.get ⟨107,by decide⟩
def sourceMap0279 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,8,9,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0279 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0279_checked : acceptsGraphIso
    (source (graph core0279) (root 9) 2 2) DegreeOneMiddleResidualSpectrum693.graph sourceMap0279=true := by decide +kernel
theorem fusedMap0279_checked : acceptsGraphIso
    (fused (graph core0279) (root 9) 2 2) DegreeTwoThreeSpectrum4107.graph fusedMap0279=true := by decide +kernel
theorem certified0279 : Certified (graph core0279) (root 9) 2 2 :=
  of_native_maps core0279 DegreeOneMiddleResidualSpectrum693.graph DegreeTwoThreeSpectrum4107.graph
    sourceMap0279 fusedMap0279 sourceMap0279_checked fusedMap0279_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0279
#print axioms sourceMap0279_checked
#print axioms fusedMap0279_checked
#print axioms certified0279
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
