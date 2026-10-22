/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0215 : Family 9 := level9.get ⟨19,by decide⟩
def sourceMap0215 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0215 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0215_checked : acceptsGraphIso
    (source (graph core0215) (root 9) 2 2) DegreeOneMiddleResidualSpectrum683.graph sourceMap0215=true := by decide +kernel
theorem fusedMap0215_checked : acceptsGraphIso
    (fused (graph core0215) (root 9) 2 2) DegreeTwoThreeSpectrum3865.graph fusedMap0215=true := by decide +kernel
theorem certified0215 : Certified (graph core0215) (root 9) 2 2 :=
  of_native_maps core0215 DegreeOneMiddleResidualSpectrum683.graph DegreeTwoThreeSpectrum3865.graph
    sourceMap0215 fusedMap0215 sourceMap0215_checked fusedMap0215_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0215
#print axioms sourceMap0215_checked
#print axioms fusedMap0215_checked
#print axioms certified0215
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
