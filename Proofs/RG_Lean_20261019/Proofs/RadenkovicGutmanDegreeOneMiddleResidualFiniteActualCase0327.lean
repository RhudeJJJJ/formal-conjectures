/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0327 : Family 9 := level9.get ⟨188,by decide⟩
def sourceMap0327 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap0327 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0327_checked : acceptsGraphIso
    (source (graph core0327) (root 9) 2 2) DegreeOneMiddleResidualSpectrum813.graph sourceMap0327=true := by decide +kernel
theorem fusedMap0327_checked : acceptsGraphIso
    (fused (graph core0327) (root 9) 2 2) DegreeTwoThreeSpectrum3960.graph fusedMap0327=true := by decide +kernel
theorem certified0327 : Certified (graph core0327) (root 9) 2 2 :=
  of_native_maps core0327 DegreeOneMiddleResidualSpectrum813.graph DegreeTwoThreeSpectrum3960.graph
    sourceMap0327 fusedMap0327 sourceMap0327_checked fusedMap0327_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0327
#print axioms sourceMap0327_checked
#print axioms fusedMap0327_checked
#print axioms certified0327
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
