/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0338 : Family 9 := level9.get ⟨209,by decide⟩
def sourceMap0338 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap0338 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0338_checked : acceptsGraphIso
    (source (graph core0338) (root 9) 2 2) DegreeOneMiddleResidualSpectrum834.graph sourceMap0338=true := by decide +kernel
theorem fusedMap0338_checked : acceptsGraphIso
    (fused (graph core0338) (root 9) 2 2) DegreeTwoThreeSpectrum3993.graph fusedMap0338=true := by decide +kernel
theorem certified0338 : Certified (graph core0338) (root 9) 2 2 :=
  of_native_maps core0338 DegreeOneMiddleResidualSpectrum834.graph DegreeTwoThreeSpectrum3993.graph
    sourceMap0338 fusedMap0338 sourceMap0338_checked fusedMap0338_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0338
#print axioms sourceMap0338_checked
#print axioms fusedMap0338_checked
#print axioms certified0338
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
