/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0237 : Family 9 := level9.get ⟨49,by decide⟩
def sourceMap0237 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0237 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0237_checked : acceptsGraphIso
    (source (graph core0237) (root 9) 2 2) DegreeOneMiddleResidualSpectrum600.graph sourceMap0237=true := by decide +kernel
theorem fusedMap0237_checked : acceptsGraphIso
    (fused (graph core0237) (root 9) 2 2) DegreeTwoThreeSpectrum3922.graph fusedMap0237=true := by decide +kernel
theorem certified0237 : Certified (graph core0237) (root 9) 2 2 :=
  of_native_maps core0237 DegreeOneMiddleResidualSpectrum600.graph DegreeTwoThreeSpectrum3922.graph
    sourceMap0237 fusedMap0237 sourceMap0237_checked fusedMap0237_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0237
#print axioms sourceMap0237_checked
#print axioms fusedMap0237_checked
#print axioms certified0237
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
