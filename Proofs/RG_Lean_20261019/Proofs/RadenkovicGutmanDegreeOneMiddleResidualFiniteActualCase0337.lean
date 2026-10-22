/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0337 : Family 9 := level9.get ⟨208,by decide⟩
def sourceMap0337 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap0337 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0337_checked : acceptsGraphIso
    (source (graph core0337) (root 9) 2 2) DegreeOneMiddleResidualSpectrum833.graph sourceMap0337=true := by decide +kernel
theorem fusedMap0337_checked : acceptsGraphIso
    (fused (graph core0337) (root 9) 2 2) DegreeTwoThreeSpectrum3992.graph fusedMap0337=true := by decide +kernel
theorem certified0337 : Certified (graph core0337) (root 9) 2 2 :=
  of_native_maps core0337 DegreeOneMiddleResidualSpectrum833.graph DegreeTwoThreeSpectrum3992.graph
    sourceMap0337 fusedMap0337 sourceMap0337_checked fusedMap0337_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0337
#print axioms sourceMap0337_checked
#print axioms fusedMap0337_checked
#print axioms certified0337
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
