/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0107 : Family 8 := level8.get ⟨65,by decide⟩
def sourceMap0107 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap0107 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0107_checked : acceptsGraphIso
    (source (graph core0107) (root 8) 2 2) DegreeOneMiddleResidualSpectrum322.graph sourceMap0107=true := by decide +kernel
theorem fusedMap0107_checked : acceptsGraphIso
    (fused (graph core0107) (root 8) 2 2) DegreeTwoThreeSpectrum2366.graph fusedMap0107=true := by decide +kernel
theorem certified0107 : Certified (graph core0107) (root 8) 2 2 :=
  of_native_maps core0107 DegreeOneMiddleResidualSpectrum322.graph DegreeTwoThreeSpectrum2366.graph
    sourceMap0107 fusedMap0107 sourceMap0107_checked fusedMap0107_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0107
#print axioms sourceMap0107_checked
#print axioms fusedMap0107_checked
#print axioms certified0107
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
