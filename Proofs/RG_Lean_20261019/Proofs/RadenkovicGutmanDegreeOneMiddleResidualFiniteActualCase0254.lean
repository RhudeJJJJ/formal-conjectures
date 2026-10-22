/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0254 : Family 9 := level9.get ⟨72,by decide⟩
def sourceMap0254 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0254 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0254_checked : acceptsGraphIso
    (source (graph core0254) (root 9) 2 2) DegreeOneMiddleResidualSpectrum652.graph sourceMap0254=true := by decide +kernel
theorem fusedMap0254_checked : acceptsGraphIso
    (fused (graph core0254) (root 9) 2 2) DegreeTwoThreeSpectrum3998.graph fusedMap0254=true := by decide +kernel
theorem certified0254 : Certified (graph core0254) (root 9) 2 2 :=
  of_native_maps core0254 DegreeOneMiddleResidualSpectrum652.graph DegreeTwoThreeSpectrum3998.graph
    sourceMap0254 fusedMap0254 sourceMap0254_checked fusedMap0254_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0254
#print axioms sourceMap0254_checked
#print axioms fusedMap0254_checked
#print axioms certified0254
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
