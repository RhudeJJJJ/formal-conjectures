/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0402 : Family 9 := level9.get ⟨343,by decide⟩
def sourceMap0402 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0402 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0402_checked : acceptsGraphIso
    (source (graph core0402) (root 9) 2 2) DegreeOneMiddleResidualSpectrum761.graph sourceMap0402=true := by decide +kernel
theorem fusedMap0402_checked : acceptsGraphIso
    (fused (graph core0402) (root 9) 2 2) DegreeTwoThreeSpectrum4239.graph fusedMap0402=true := by decide +kernel
theorem certified0402 : Certified (graph core0402) (root 9) 2 2 :=
  of_native_maps core0402 DegreeOneMiddleResidualSpectrum761.graph DegreeTwoThreeSpectrum4239.graph
    sourceMap0402 fusedMap0402 sourceMap0402_checked fusedMap0402_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0402
#print axioms sourceMap0402_checked
#print axioms fusedMap0402_checked
#print axioms certified0402
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
