/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0303 : Family 9 := level9.get ⟨149,by decide⟩
def sourceMap0303 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0303 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0303_checked : acceptsGraphIso
    (source (graph core0303) (root 9) 2 2) DegreeOneMiddleResidualSpectrum766.graph sourceMap0303=true := by decide +kernel
theorem fusedMap0303_checked : acceptsGraphIso
    (fused (graph core0303) (root 9) 2 2) DegreeTwoThreeSpectrum3905.graph fusedMap0303=true := by decide +kernel
theorem certified0303 : Certified (graph core0303) (root 9) 2 2 :=
  of_native_maps core0303 DegreeOneMiddleResidualSpectrum766.graph DegreeTwoThreeSpectrum3905.graph
    sourceMap0303 fusedMap0303 sourceMap0303_checked fusedMap0303_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0303
#print axioms sourceMap0303_checked
#print axioms fusedMap0303_checked
#print axioms certified0303
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
