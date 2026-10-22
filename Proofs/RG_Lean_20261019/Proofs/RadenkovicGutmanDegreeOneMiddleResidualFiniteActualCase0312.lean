/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0312 : Family 9 := level9.get ⟨163,by decide⟩
def sourceMap0312 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0312 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0312_checked : acceptsGraphIso
    (source (graph core0312) (root 9) 2 2) DegreeOneMiddleResidualSpectrum786.graph sourceMap0312=true := by decide +kernel
theorem fusedMap0312_checked : acceptsGraphIso
    (fused (graph core0312) (root 9) 2 2) DegreeTwoThreeSpectrum3924.graph fusedMap0312=true := by decide +kernel
theorem certified0312 : Certified (graph core0312) (root 9) 2 2 :=
  of_native_maps core0312 DegreeOneMiddleResidualSpectrum786.graph DegreeTwoThreeSpectrum3924.graph
    sourceMap0312 fusedMap0312 sourceMap0312_checked fusedMap0312_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0312
#print axioms sourceMap0312_checked
#print axioms fusedMap0312_checked
#print axioms certified0312
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
