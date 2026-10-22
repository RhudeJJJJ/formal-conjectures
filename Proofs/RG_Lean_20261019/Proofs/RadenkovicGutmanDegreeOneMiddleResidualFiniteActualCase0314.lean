/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0314 : Family 9 := level9.get ⟨166,by decide⟩
def sourceMap0314 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0314 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0314_checked : acceptsGraphIso
    (source (graph core0314) (root 9) 2 2) DegreeOneMiddleResidualSpectrum792.graph sourceMap0314=true := by decide +kernel
theorem fusedMap0314_checked : acceptsGraphIso
    (fused (graph core0314) (root 9) 2 2) DegreeTwoThreeSpectrum3928.graph fusedMap0314=true := by decide +kernel
theorem certified0314 : Certified (graph core0314) (root 9) 2 2 :=
  of_native_maps core0314 DegreeOneMiddleResidualSpectrum792.graph DegreeTwoThreeSpectrum3928.graph
    sourceMap0314 fusedMap0314 sourceMap0314_checked fusedMap0314_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0314
#print axioms sourceMap0314_checked
#print axioms fusedMap0314_checked
#print axioms certified0314
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
