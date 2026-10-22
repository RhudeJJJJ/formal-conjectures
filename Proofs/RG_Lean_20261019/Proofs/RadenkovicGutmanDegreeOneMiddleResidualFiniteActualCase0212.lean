/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0212 : Family 9 := level9.get ⟨16,by decide⟩
def sourceMap0212 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0212 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0212_checked : acceptsGraphIso
    (source (graph core0212) (root 9) 2 2) DegreeOneMiddleResidualSpectrum653.graph sourceMap0212=true := by decide +kernel
theorem fusedMap0212_checked : acceptsGraphIso
    (fused (graph core0212) (root 9) 2 2) DegreeTwoThreeSpectrum3862.graph fusedMap0212=true := by decide +kernel
theorem certified0212 : Certified (graph core0212) (root 9) 2 2 :=
  of_native_maps core0212 DegreeOneMiddleResidualSpectrum653.graph DegreeTwoThreeSpectrum3862.graph
    sourceMap0212 fusedMap0212 sourceMap0212_checked fusedMap0212_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0212
#print axioms sourceMap0212_checked
#print axioms fusedMap0212_checked
#print axioms certified0212
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
