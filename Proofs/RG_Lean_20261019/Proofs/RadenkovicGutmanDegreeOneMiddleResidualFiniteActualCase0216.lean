/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0216 : Family 9 := level9.get ⟨20,by decide⟩
def sourceMap0216 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0216 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0216_checked : acceptsGraphIso
    (source (graph core0216) (root 9) 2 2) DegreeOneMiddleResidualSpectrum687.graph sourceMap0216=true := by decide +kernel
theorem fusedMap0216_checked : acceptsGraphIso
    (fused (graph core0216) (root 9) 2 2) DegreeTwoThreeSpectrum3866.graph fusedMap0216=true := by decide +kernel
theorem certified0216 : Certified (graph core0216) (root 9) 2 2 :=
  of_native_maps core0216 DegreeOneMiddleResidualSpectrum687.graph DegreeTwoThreeSpectrum3866.graph
    sourceMap0216 fusedMap0216 sourceMap0216_checked fusedMap0216_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0216
#print axioms sourceMap0216_checked
#print axioms fusedMap0216_checked
#print axioms certified0216
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
