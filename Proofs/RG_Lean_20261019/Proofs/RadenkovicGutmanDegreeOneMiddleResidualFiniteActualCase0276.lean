/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0276 : Family 9 := level9.get ⟨103,by decide⟩
def sourceMap0276 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0276 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0276_checked : acceptsGraphIso
    (source (graph core0276) (root 9) 2 2) DegreeOneMiddleResidualSpectrum716.graph sourceMap0276=true := by decide +kernel
theorem fusedMap0276_checked : acceptsGraphIso
    (fused (graph core0276) (root 9) 2 2) DegreeTwoThreeSpectrum4096.graph fusedMap0276=true := by decide +kernel
theorem certified0276 : Certified (graph core0276) (root 9) 2 2 :=
  of_native_maps core0276 DegreeOneMiddleResidualSpectrum716.graph DegreeTwoThreeSpectrum4096.graph
    sourceMap0276 fusedMap0276 sourceMap0276_checked fusedMap0276_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0276
#print axioms sourceMap0276_checked
#print axioms fusedMap0276_checked
#print axioms certified0276
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
