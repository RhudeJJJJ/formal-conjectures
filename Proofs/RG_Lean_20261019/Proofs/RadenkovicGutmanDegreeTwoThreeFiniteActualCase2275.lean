/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2275 : Family 9 := level9.get ⟨224,by decide⟩
def sourceMap2275 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2275 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2275_checked : acceptsGraphIso
    (source (graph core2275) (root 9) 0 4) DegreeTwoThreeSpectrum4480.graph sourceMap2275=true := by decide +kernel
theorem fusedMap2275_checked : acceptsGraphIso
    (fused (graph core2275) (root 9) 0 4) DegreeTwoThreeSpectrum4013.graph fusedMap2275=true := by decide +kernel
theorem certified2275 : Certified (graph core2275) (root 9) 0 4 :=
  of_native_maps core2275 DegreeTwoThreeSpectrum4480.graph DegreeTwoThreeSpectrum4013.graph
    sourceMap2275 fusedMap2275 sourceMap2275_checked fusedMap2275_checked
    DegreeTwoThreeFiniteComparisons.comparison2275
#print axioms sourceMap2275_checked
#print axioms fusedMap2275_checked
#print axioms certified2275
def sourceMap2275swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2275swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2275swap_checked : acceptsGraphIso
    (source (graph core2275) (root 9) 4 0) DegreeTwoThreeSpectrum4480.graph sourceMap2275swap=true := by decide +kernel
theorem fusedMap2275swap_checked : acceptsGraphIso
    (fused (graph core2275) (root 9) 4 0) DegreeTwoThreeSpectrum4013.graph fusedMap2275swap=true := by decide +kernel
theorem certified2275swap : Certified (graph core2275) (root 9) 4 0 :=
  of_native_maps core2275 DegreeTwoThreeSpectrum4480.graph DegreeTwoThreeSpectrum4013.graph
    sourceMap2275swap fusedMap2275swap sourceMap2275swap_checked fusedMap2275swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2275
#print axioms sourceMap2275swap_checked
#print axioms fusedMap2275swap_checked
#print axioms certified2275swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
