/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0336 : Family 9 := level9.get ⟨206,by decide⟩
def sourceMap0336 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0336 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0336_checked : acceptsGraphIso
    (source (graph core0336) (root 9) 2 2) DegreeOneMiddleResidualSpectrum832.graph sourceMap0336=true := by decide +kernel
theorem fusedMap0336_checked : acceptsGraphIso
    (fused (graph core0336) (root 9) 2 2) DegreeTwoThreeSpectrum3989.graph fusedMap0336=true := by decide +kernel
theorem certified0336 : Certified (graph core0336) (root 9) 2 2 :=
  of_native_maps core0336 DegreeOneMiddleResidualSpectrum832.graph DegreeTwoThreeSpectrum3989.graph
    sourceMap0336 fusedMap0336 sourceMap0336_checked fusedMap0336_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0336
#print axioms sourceMap0336_checked
#print axioms fusedMap0336_checked
#print axioms certified0336
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
