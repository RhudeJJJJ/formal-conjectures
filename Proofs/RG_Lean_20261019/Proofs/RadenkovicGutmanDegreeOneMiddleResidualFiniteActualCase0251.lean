/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0251 : Family 9 := level9.get ⟨69,by decide⟩
def sourceMap0251 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0251 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0251_checked : acceptsGraphIso
    (source (graph core0251) (root 9) 2 2) DegreeOneMiddleResidualSpectrum645.graph sourceMap0251=true := by decide +kernel
theorem fusedMap0251_checked : acceptsGraphIso
    (fused (graph core0251) (root 9) 2 2) DegreeTwoThreeSpectrum3986.graph fusedMap0251=true := by decide +kernel
theorem certified0251 : Certified (graph core0251) (root 9) 2 2 :=
  of_native_maps core0251 DegreeOneMiddleResidualSpectrum645.graph DegreeTwoThreeSpectrum3986.graph
    sourceMap0251 fusedMap0251 sourceMap0251_checked fusedMap0251_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0251
#print axioms sourceMap0251_checked
#print axioms fusedMap0251_checked
#print axioms certified0251
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
