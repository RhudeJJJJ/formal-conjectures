/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0313 : Family 9 := level9.get ⟨165,by decide⟩
def sourceMap0313 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0313 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0313_checked : acceptsGraphIso
    (source (graph core0313) (root 9) 2 2) DegreeOneMiddleResidualSpectrum790.graph sourceMap0313=true := by decide +kernel
theorem fusedMap0313_checked : acceptsGraphIso
    (fused (graph core0313) (root 9) 2 2) DegreeTwoThreeSpectrum3927.graph fusedMap0313=true := by decide +kernel
theorem certified0313 : Certified (graph core0313) (root 9) 2 2 :=
  of_native_maps core0313 DegreeOneMiddleResidualSpectrum790.graph DegreeTwoThreeSpectrum3927.graph
    sourceMap0313 fusedMap0313 sourceMap0313_checked fusedMap0313_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0313
#print axioms sourceMap0313_checked
#print axioms fusedMap0313_checked
#print axioms certified0313
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
