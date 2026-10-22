/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0089 : Family 8 := level8.get ⟨39,by decide⟩
def sourceMap0089 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0089 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0089_checked : acceptsGraphIso
    (source (graph core0089) (root 8) 2 2) DegreeOneMiddleResidualSpectrum280.graph sourceMap0089=true := by decide +kernel
theorem fusedMap0089_checked : acceptsGraphIso
    (fused (graph core0089) (root 8) 2 2) DegreeTwoThreeSpectrum2321.graph fusedMap0089=true := by decide +kernel
theorem certified0089 : Certified (graph core0089) (root 8) 2 2 :=
  of_native_maps core0089 DegreeOneMiddleResidualSpectrum280.graph DegreeTwoThreeSpectrum2321.graph
    sourceMap0089 fusedMap0089 sourceMap0089_checked fusedMap0089_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0089
#print axioms sourceMap0089_checked
#print axioms fusedMap0089_checked
#print axioms certified0089
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
