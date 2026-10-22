/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0209 : Family 9 := level9.get ⟨12,by decide⟩
def sourceMap0209 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0209 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0209_checked : acceptsGraphIso
    (source (graph core0209) (root 9) 2 2) DegreeOneMiddleResidualSpectrum631.graph sourceMap0209=true := by decide +kernel
theorem fusedMap0209_checked : acceptsGraphIso
    (fused (graph core0209) (root 9) 2 2) DegreeTwoThreeSpectrum3857.graph fusedMap0209=true := by decide +kernel
theorem certified0209 : Certified (graph core0209) (root 9) 2 2 :=
  of_native_maps core0209 DegreeOneMiddleResidualSpectrum631.graph DegreeTwoThreeSpectrum3857.graph
    sourceMap0209 fusedMap0209 sourceMap0209_checked fusedMap0209_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0209
#print axioms sourceMap0209_checked
#print axioms fusedMap0209_checked
#print axioms certified0209
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
