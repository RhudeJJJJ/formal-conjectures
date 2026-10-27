/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4337 : Family 9 := level9.get ⟨449,by decide⟩
def sourceMap4337 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4337 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4337_checked : acceptsGraphIso
    (source (graph core4337) (root 9) 2 2) DegreeTwoThreeSpectrum4828.graph sourceMap4337=true := by decide +kernel
theorem fusedMap4337_checked : acceptsGraphIso
    (fused (graph core4337) (root 9) 2 2) DegreeTwoThreeSpectrum4465.graph fusedMap4337=true := by decide +kernel
theorem certified4337 : Certified (graph core4337) (root 9) 2 2 :=
  of_native_maps core4337 DegreeTwoThreeSpectrum4828.graph DegreeTwoThreeSpectrum4465.graph
    sourceMap4337 fusedMap4337 sourceMap4337_checked fusedMap4337_checked
    DegreeTwoThreeFiniteComparisons.comparison4337
#print axioms sourceMap4337_checked
#print axioms fusedMap4337_checked
#print axioms certified4337
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
