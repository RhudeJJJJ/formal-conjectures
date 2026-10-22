/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0417 : Family 9 := level9.get ⟨375,by decide⟩
def sourceMap0417 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0417 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0417_checked : acceptsGraphIso
    (source (graph core0417) (root 9) 2 2) DegreeOneMiddleResidualSpectrum788.graph sourceMap0417=true := by decide +kernel
theorem fusedMap0417_checked : acceptsGraphIso
    (fused (graph core0417) (root 9) 2 2) DegreeTwoThreeSpectrum4309.graph fusedMap0417=true := by decide +kernel
theorem certified0417 : Certified (graph core0417) (root 9) 2 2 :=
  of_native_maps core0417 DegreeOneMiddleResidualSpectrum788.graph DegreeTwoThreeSpectrum4309.graph
    sourceMap0417 fusedMap0417 sourceMap0417_checked fusedMap0417_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0417
#print axioms sourceMap0417_checked
#print axioms fusedMap0417_checked
#print axioms certified0417
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
