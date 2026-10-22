/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0311 : Family 9 := level9.get ⟨162,by decide⟩
def sourceMap0311 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0311 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0311_checked : acceptsGraphIso
    (source (graph core0311) (root 9) 2 2) DegreeOneMiddleResidualSpectrum785.graph sourceMap0311=true := by decide +kernel
theorem fusedMap0311_checked : acceptsGraphIso
    (fused (graph core0311) (root 9) 2 2) DegreeTwoThreeSpectrum3923.graph fusedMap0311=true := by decide +kernel
theorem certified0311 : Certified (graph core0311) (root 9) 2 2 :=
  of_native_maps core0311 DegreeOneMiddleResidualSpectrum785.graph DegreeTwoThreeSpectrum3923.graph
    sourceMap0311 fusedMap0311 sourceMap0311_checked fusedMap0311_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0311
#print axioms sourceMap0311_checked
#print axioms fusedMap0311_checked
#print axioms certified0311
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
