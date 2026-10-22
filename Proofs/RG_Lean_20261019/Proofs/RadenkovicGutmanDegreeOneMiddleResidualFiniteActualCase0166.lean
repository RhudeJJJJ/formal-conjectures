/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0166 : Family 8 := level8.get ⟨207,by decide⟩
def sourceMap0166 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0166 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0166_checked : acceptsGraphIso
    (source (graph core0166) (root 8) 2 2) DegreeOneMiddleResidualSpectrum350.graph sourceMap0166=true := by decide +kernel
theorem fusedMap0166_checked : acceptsGraphIso
    (fused (graph core0166) (root 8) 2 2) DegreeTwoThreeSpectrum2502.graph fusedMap0166=true := by decide +kernel
theorem certified0166 : Certified (graph core0166) (root 8) 2 2 :=
  of_native_maps core0166 DegreeOneMiddleResidualSpectrum350.graph DegreeTwoThreeSpectrum2502.graph
    sourceMap0166 fusedMap0166 sourceMap0166_checked fusedMap0166_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0166
#print axioms sourceMap0166_checked
#print axioms fusedMap0166_checked
#print axioms certified0166
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
