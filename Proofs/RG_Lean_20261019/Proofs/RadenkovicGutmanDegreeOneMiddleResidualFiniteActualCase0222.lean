/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0222 : Family 9 := level9.get ⟨27,by decide⟩
def sourceMap0222 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,10,11,12,13,14,15,9,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap0222 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0222_checked : acceptsGraphIso
    (source (graph core0222) (root 9) 2 2) DegreeOneMiddleResidualSpectrum703.graph sourceMap0222=true := by decide +kernel
theorem fusedMap0222_checked : acceptsGraphIso
    (fused (graph core0222) (root 9) 2 2) DegreeTwoThreeSpectrum3874.graph fusedMap0222=true := by decide +kernel
theorem certified0222 : Certified (graph core0222) (root 9) 2 2 :=
  of_native_maps core0222 DegreeOneMiddleResidualSpectrum703.graph DegreeTwoThreeSpectrum3874.graph
    sourceMap0222 fusedMap0222 sourceMap0222_checked fusedMap0222_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0222
#print axioms sourceMap0222_checked
#print axioms fusedMap0222_checked
#print axioms certified0222
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
