/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0324 : Family 9 := level9.get ⟨182,by decide⟩
def sourceMap0324 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap0324 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0324_checked : acceptsGraphIso
    (source (graph core0324) (root 9) 2 2) DegreeOneMiddleResidualSpectrum810.graph sourceMap0324=true := by decide +kernel
theorem fusedMap0324_checked : acceptsGraphIso
    (fused (graph core0324) (root 9) 2 2) DegreeTwoThreeSpectrum3950.graph fusedMap0324=true := by decide +kernel
theorem certified0324 : Certified (graph core0324) (root 9) 2 2 :=
  of_native_maps core0324 DegreeOneMiddleResidualSpectrum810.graph DegreeTwoThreeSpectrum3950.graph
    sourceMap0324 fusedMap0324 sourceMap0324_checked fusedMap0324_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0324
#print axioms sourceMap0324_checked
#print axioms fusedMap0324_checked
#print axioms certified0324
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
