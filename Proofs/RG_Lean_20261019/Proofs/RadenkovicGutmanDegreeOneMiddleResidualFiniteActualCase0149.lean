/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0149 : Family 8 := level8.get ⟨149,by decide⟩
def sourceMap0149 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0149 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0149_checked : acceptsGraphIso
    (source (graph core0149) (root 8) 2 2) DegreeOneMiddleResidualSpectrum315.graph sourceMap0149=true := by decide +kernel
theorem fusedMap0149_checked : acceptsGraphIso
    (fused (graph core0149) (root 8) 2 2) DegreeTwoThreeSpectrum2734.graph fusedMap0149=true := by decide +kernel
theorem certified0149 : Certified (graph core0149) (root 8) 2 2 :=
  of_native_maps core0149 DegreeOneMiddleResidualSpectrum315.graph DegreeTwoThreeSpectrum2734.graph
    sourceMap0149 fusedMap0149 sourceMap0149_checked fusedMap0149_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0149
#print axioms sourceMap0149_checked
#print axioms fusedMap0149_checked
#print axioms certified0149
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
