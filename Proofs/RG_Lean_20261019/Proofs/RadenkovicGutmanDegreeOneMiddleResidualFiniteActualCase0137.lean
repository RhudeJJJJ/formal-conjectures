/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0137 : Family 8 := level8.get ⟨121,by decide⟩
def sourceMap0137 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0137 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0137_checked : acceptsGraphIso
    (source (graph core0137) (root 8) 2 2) DegreeOneMiddleResidualSpectrum290.graph sourceMap0137=true := by decide +kernel
theorem fusedMap0137_checked : acceptsGraphIso
    (fused (graph core0137) (root 8) 2 2) DegreeTwoThreeSpectrum2569.graph fusedMap0137=true := by decide +kernel
theorem certified0137 : Certified (graph core0137) (root 8) 2 2 :=
  of_native_maps core0137 DegreeOneMiddleResidualSpectrum290.graph DegreeTwoThreeSpectrum2569.graph
    sourceMap0137 fusedMap0137 sourceMap0137_checked fusedMap0137_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0137
#print axioms sourceMap0137_checked
#print axioms fusedMap0137_checked
#print axioms certified0137
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
