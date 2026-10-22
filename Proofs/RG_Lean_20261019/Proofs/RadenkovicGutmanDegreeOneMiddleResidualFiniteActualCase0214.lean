/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0214 : Family 9 := level9.get ⟨18,by decide⟩
def sourceMap0214 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0214 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0214_checked : acceptsGraphIso
    (source (graph core0214) (root 9) 2 2) DegreeOneMiddleResidualSpectrum679.graph sourceMap0214=true := by decide +kernel
theorem fusedMap0214_checked : acceptsGraphIso
    (fused (graph core0214) (root 9) 2 2) DegreeTwoThreeSpectrum3864.graph fusedMap0214=true := by decide +kernel
theorem certified0214 : Certified (graph core0214) (root 9) 2 2 :=
  of_native_maps core0214 DegreeOneMiddleResidualSpectrum679.graph DegreeTwoThreeSpectrum3864.graph
    sourceMap0214 fusedMap0214 sourceMap0214_checked fusedMap0214_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0214
#print axioms sourceMap0214_checked
#print axioms fusedMap0214_checked
#print axioms certified0214
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
