/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0306 : Family 9 := level9.get ⟨156,by decide⟩
def sourceMap0306 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0306 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0306_checked : acceptsGraphIso
    (source (graph core0306) (root 9) 2 2) DegreeOneMiddleResidualSpectrum771.graph sourceMap0306=true := by decide +kernel
theorem fusedMap0306_checked : acceptsGraphIso
    (fused (graph core0306) (root 9) 2 2) DegreeTwoThreeSpectrum3917.graph fusedMap0306=true := by decide +kernel
theorem certified0306 : Certified (graph core0306) (root 9) 2 2 :=
  of_native_maps core0306 DegreeOneMiddleResidualSpectrum771.graph DegreeTwoThreeSpectrum3917.graph
    sourceMap0306 fusedMap0306 sourceMap0306_checked fusedMap0306_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0306
#print axioms sourceMap0306_checked
#print axioms fusedMap0306_checked
#print axioms certified0306
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
