/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0357 : Family 9 := level9.get ⟨241,by decide⟩
def sourceMap0357 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap0357 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0357_checked : acceptsGraphIso
    (source (graph core0357) (root 9) 2 2) DegreeOneMiddleResidualSpectrum868.graph sourceMap0357=true := by decide +kernel
theorem fusedMap0357_checked : acceptsGraphIso
    (fused (graph core0357) (root 9) 2 2) DegreeTwoThreeSpectrum4038.graph fusedMap0357=true := by decide +kernel
theorem certified0357 : Certified (graph core0357) (root 9) 2 2 :=
  of_native_maps core0357 DegreeOneMiddleResidualSpectrum868.graph DegreeTwoThreeSpectrum4038.graph
    sourceMap0357 fusedMap0357 sourceMap0357_checked fusedMap0357_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0357
#print axioms sourceMap0357_checked
#print axioms fusedMap0357_checked
#print axioms certified0357
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
