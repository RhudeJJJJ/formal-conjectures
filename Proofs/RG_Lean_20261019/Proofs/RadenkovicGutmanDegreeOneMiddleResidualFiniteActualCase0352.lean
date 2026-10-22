/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0352 : Family 9 := level9.get ⟨232,by decide⟩
def sourceMap0352 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0352 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0352_checked : acceptsGraphIso
    (source (graph core0352) (root 9) 2 2) DegreeOneMiddleResidualSpectrum863.graph sourceMap0352=true := by decide +kernel
theorem fusedMap0352_checked : acceptsGraphIso
    (fused (graph core0352) (root 9) 2 2) DegreeTwoThreeSpectrum4024.graph fusedMap0352=true := by decide +kernel
theorem certified0352 : Certified (graph core0352) (root 9) 2 2 :=
  of_native_maps core0352 DegreeOneMiddleResidualSpectrum863.graph DegreeTwoThreeSpectrum4024.graph
    sourceMap0352 fusedMap0352 sourceMap0352_checked fusedMap0352_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0352
#print axioms sourceMap0352_checked
#print axioms fusedMap0352_checked
#print axioms certified0352
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
