/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0218 : Family 9 := level9.get ⟨220,by decide⟩
def sourceMap0218 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0218 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0218_checked : acceptsGraphIso
    (source (graph core0218) (root 9) 0 0) DegreeTwoThreeSpectrum590.graph sourceMap0218=true := by decide +kernel
theorem fusedMap0218_checked : acceptsGraphIso
    (fused (graph core0218) (root 9) 0 0) DegreeOneSmallSpectrum526.graph fusedMap0218=true := by decide +kernel
theorem certified0218 : Certified (graph core0218) (root 9) 0 0 :=
  of_native_maps core0218 DegreeTwoThreeSpectrum590.graph DegreeOneSmallSpectrum526.graph
    sourceMap0218 fusedMap0218 sourceMap0218_checked fusedMap0218_checked
    DegreeTwoThreeFiniteComparisons.comparison0218
#print axioms sourceMap0218_checked
#print axioms fusedMap0218_checked
#print axioms certified0218
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
