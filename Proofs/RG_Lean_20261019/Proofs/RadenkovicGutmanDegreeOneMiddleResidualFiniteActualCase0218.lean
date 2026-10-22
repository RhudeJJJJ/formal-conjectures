/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0218 : Family 9 := level9.get ⟨23,by decide⟩
def sourceMap0218 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap0218 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0218_checked : acceptsGraphIso
    (source (graph core0218) (root 9) 2 2) DegreeOneMiddleResidualSpectrum712.graph sourceMap0218=true := by decide +kernel
theorem fusedMap0218_checked : acceptsGraphIso
    (fused (graph core0218) (root 9) 2 2) DegreeTwoThreeSpectrum3870.graph fusedMap0218=true := by decide +kernel
theorem certified0218 : Certified (graph core0218) (root 9) 2 2 :=
  of_native_maps core0218 DegreeOneMiddleResidualSpectrum712.graph DegreeTwoThreeSpectrum3870.graph
    sourceMap0218 fusedMap0218 sourceMap0218_checked fusedMap0218_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0218
#print axioms sourceMap0218_checked
#print axioms fusedMap0218_checked
#print axioms certified0218
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
