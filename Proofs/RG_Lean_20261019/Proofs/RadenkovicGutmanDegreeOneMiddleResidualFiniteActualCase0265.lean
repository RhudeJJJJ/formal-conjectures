/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0265 : Family 9 := level9.get ⟨86,by decide⟩
def sourceMap0265 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0265 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0265_checked : acceptsGraphIso
    (source (graph core0265) (root 9) 2 2) DegreeOneMiddleResidualSpectrum682.graph sourceMap0265=true := by decide +kernel
theorem fusedMap0265_checked : acceptsGraphIso
    (fused (graph core0265) (root 9) 2 2) DegreeTwoThreeSpectrum4045.graph fusedMap0265=true := by decide +kernel
theorem certified0265 : Certified (graph core0265) (root 9) 2 2 :=
  of_native_maps core0265 DegreeOneMiddleResidualSpectrum682.graph DegreeTwoThreeSpectrum4045.graph
    sourceMap0265 fusedMap0265 sourceMap0265_checked fusedMap0265_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0265
#print axioms sourceMap0265_checked
#print axioms fusedMap0265_checked
#print axioms certified0265
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
