/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0304 : Family 9 := level9.get ⟨151,by decide⟩
def sourceMap0304 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap0304 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0304_checked : acceptsGraphIso
    (source (graph core0304) (root 9) 2 2) DegreeOneMiddleResidualSpectrum767.graph sourceMap0304=true := by decide +kernel
theorem fusedMap0304_checked : acceptsGraphIso
    (fused (graph core0304) (root 9) 2 2) DegreeTwoThreeSpectrum3908.graph fusedMap0304=true := by decide +kernel
theorem certified0304 : Certified (graph core0304) (root 9) 2 2 :=
  of_native_maps core0304 DegreeOneMiddleResidualSpectrum767.graph DegreeTwoThreeSpectrum3908.graph
    sourceMap0304 fusedMap0304 sourceMap0304_checked fusedMap0304_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0304
#print axioms sourceMap0304_checked
#print axioms fusedMap0304_checked
#print axioms certified0304
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
