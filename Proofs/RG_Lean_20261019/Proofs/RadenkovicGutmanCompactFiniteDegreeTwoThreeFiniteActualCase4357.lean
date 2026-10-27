/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4357 : Family 9 := level9.get ⟨496,by decide⟩
def sourceMap4357 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,8,9,10,11,12,13,14,15,7,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4357 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4357_checked : acceptsGraphIso
    (source (graph core4357) (root 9) 2 2) DegreeTwoThreeSpectrum4885.graph sourceMap4357=true := by decide +kernel
theorem fusedMap4357_checked : acceptsGraphIso
    (fused (graph core4357) (root 9) 2 2) DegreeTwoThreeSpectrum4572.graph fusedMap4357=true := by decide +kernel
theorem certified4357 : Certified (graph core4357) (root 9) 2 2 :=
  of_native_maps core4357 DegreeTwoThreeSpectrum4885.graph DegreeTwoThreeSpectrum4572.graph
    sourceMap4357 fusedMap4357 sourceMap4357_checked fusedMap4357_checked
    DegreeTwoThreeFiniteComparisons.comparison4357
#print axioms sourceMap4357_checked
#print axioms fusedMap4357_checked
#print axioms certified4357
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
