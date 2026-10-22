/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2234 : Family 9 := level9.get ⟨91,by decide⟩
def sourceMap2234 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2234 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 0 4 v)
theorem sourceMap2234_checked : acceptsGraphIso
    (source (graph core2234) (root 9) 0 4) DegreeTwoThreeSpectrum4055.graph sourceMap2234=true := by decide +kernel
theorem fusedMap2234_checked : acceptsGraphIso
    (fused (graph core2234) (root 9) 0 4) DegreeTwoThreeSpectrum4057.graph fusedMap2234=true := by decide +kernel
theorem certified2234 : Certified (graph core2234) (root 9) 0 4 :=
  of_native_maps core2234 DegreeTwoThreeSpectrum4055.graph DegreeTwoThreeSpectrum4057.graph
    sourceMap2234 fusedMap2234 sourceMap2234_checked fusedMap2234_checked
    DegreeTwoThreeFiniteComparisons.comparison2234
#print axioms sourceMap2234_checked
#print axioms fusedMap2234_checked
#print axioms certified2234
def sourceMap2234swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2234swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 4 0 v)
theorem sourceMap2234swap_checked : acceptsGraphIso
    (source (graph core2234) (root 9) 4 0) DegreeTwoThreeSpectrum4055.graph sourceMap2234swap=true := by decide +kernel
theorem fusedMap2234swap_checked : acceptsGraphIso
    (fused (graph core2234) (root 9) 4 0) DegreeTwoThreeSpectrum4057.graph fusedMap2234swap=true := by decide +kernel
theorem certified2234swap : Certified (graph core2234) (root 9) 4 0 :=
  of_native_maps core2234 DegreeTwoThreeSpectrum4055.graph DegreeTwoThreeSpectrum4057.graph
    sourceMap2234swap fusedMap2234swap sourceMap2234swap_checked fusedMap2234swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2234
#print axioms sourceMap2234swap_checked
#print axioms fusedMap2234swap_checked
#print axioms certified2234swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
