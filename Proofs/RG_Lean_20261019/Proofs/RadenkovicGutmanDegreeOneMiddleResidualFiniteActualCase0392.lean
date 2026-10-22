/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0392 : Family 9 := level9.get ⟨325,by decide⟩
def sourceMap0392 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0392 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0392_checked : acceptsGraphIso
    (source (graph core0392) (root 9) 2 2) DegreeOneMiddleResidualSpectrum745.graph sourceMap0392=true := by decide +kernel
theorem fusedMap0392_checked : acceptsGraphIso
    (fused (graph core0392) (root 9) 2 2) DegreeTwoThreeSpectrum4196.graph fusedMap0392=true := by decide +kernel
theorem certified0392 : Certified (graph core0392) (root 9) 2 2 :=
  of_native_maps core0392 DegreeOneMiddleResidualSpectrum745.graph DegreeTwoThreeSpectrum4196.graph
    sourceMap0392 fusedMap0392 sourceMap0392_checked fusedMap0392_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0392
#print axioms sourceMap0392_checked
#print axioms fusedMap0392_checked
#print axioms certified0392
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
