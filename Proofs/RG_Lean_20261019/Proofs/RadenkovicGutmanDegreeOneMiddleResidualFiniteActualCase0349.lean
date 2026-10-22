/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0349 : Family 9 := level9.get ⟨228,by decide⟩
def sourceMap0349 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0349 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0349_checked : acceptsGraphIso
    (source (graph core0349) (root 9) 2 2) DegreeOneMiddleResidualSpectrum859.graph sourceMap0349=true := by decide +kernel
theorem fusedMap0349_checked : acceptsGraphIso
    (fused (graph core0349) (root 9) 2 2) DegreeTwoThreeSpectrum4020.graph fusedMap0349=true := by decide +kernel
theorem certified0349 : Certified (graph core0349) (root 9) 2 2 :=
  of_native_maps core0349 DegreeOneMiddleResidualSpectrum859.graph DegreeTwoThreeSpectrum4020.graph
    sourceMap0349 fusedMap0349 sourceMap0349_checked fusedMap0349_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0349
#print axioms sourceMap0349_checked
#print axioms fusedMap0349_checked
#print axioms certified0349
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
