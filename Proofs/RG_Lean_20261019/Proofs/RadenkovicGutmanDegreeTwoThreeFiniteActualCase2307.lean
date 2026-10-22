/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2307 : Family 9 := level9.get ⟨309,by decide⟩
def sourceMap2307 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,6,7,8,9,10] (sourceLabel 9 0 4 v)
def fusedMap2307 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2307_checked : acceptsGraphIso
    (source (graph core2307) (root 9) 0 4) DegreeTwoThreeSpectrum4659.graph sourceMap2307=true := by decide +kernel
theorem fusedMap2307_checked : acceptsGraphIso
    (fused (graph core2307) (root 9) 0 4) DegreeTwoThreeSpectrum4151.graph fusedMap2307=true := by decide +kernel
theorem certified2307 : Certified (graph core2307) (root 9) 0 4 :=
  of_native_maps core2307 DegreeTwoThreeSpectrum4659.graph DegreeTwoThreeSpectrum4151.graph
    sourceMap2307 fusedMap2307 sourceMap2307_checked fusedMap2307_checked
    DegreeTwoThreeFiniteComparisons.comparison2307
#print axioms sourceMap2307_checked
#print axioms fusedMap2307_checked
#print axioms certified2307
def sourceMap2307swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,6,7,8,9,10,15] (sourceLabel 9 4 0 v)
def fusedMap2307swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2307swap_checked : acceptsGraphIso
    (source (graph core2307) (root 9) 4 0) DegreeTwoThreeSpectrum4659.graph sourceMap2307swap=true := by decide +kernel
theorem fusedMap2307swap_checked : acceptsGraphIso
    (fused (graph core2307) (root 9) 4 0) DegreeTwoThreeSpectrum4151.graph fusedMap2307swap=true := by decide +kernel
theorem certified2307swap : Certified (graph core2307) (root 9) 4 0 :=
  of_native_maps core2307 DegreeTwoThreeSpectrum4659.graph DegreeTwoThreeSpectrum4151.graph
    sourceMap2307swap fusedMap2307swap sourceMap2307swap_checked fusedMap2307swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2307
#print axioms sourceMap2307swap_checked
#print axioms fusedMap2307swap_checked
#print axioms certified2307swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
