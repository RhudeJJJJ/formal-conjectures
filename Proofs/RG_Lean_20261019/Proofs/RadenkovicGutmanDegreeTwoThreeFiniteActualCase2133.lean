/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2133 : Family 8 := level8.get ⟨64,by decide⟩
def sourceMap2133 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2133 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2133_checked : acceptsGraphIso
    (source (graph core2133) (root 8) 0 4) DegreeTwoThreeSpectrum2770.graph sourceMap2133=true := by decide +kernel
theorem fusedMap2133_checked : acceptsGraphIso
    (fused (graph core2133) (root 8) 0 4) DegreeTwoThreeSpectrum2363.graph fusedMap2133=true := by decide +kernel
theorem certified2133 : Certified (graph core2133) (root 8) 0 4 :=
  of_native_maps core2133 DegreeTwoThreeSpectrum2770.graph DegreeTwoThreeSpectrum2363.graph
    sourceMap2133 fusedMap2133 sourceMap2133_checked fusedMap2133_checked
    DegreeTwoThreeFiniteComparisons.comparison2133
#print axioms sourceMap2133_checked
#print axioms fusedMap2133_checked
#print axioms certified2133
def sourceMap2133swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2133swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2133swap_checked : acceptsGraphIso
    (source (graph core2133) (root 8) 4 0) DegreeTwoThreeSpectrum2770.graph sourceMap2133swap=true := by decide +kernel
theorem fusedMap2133swap_checked : acceptsGraphIso
    (fused (graph core2133) (root 8) 4 0) DegreeTwoThreeSpectrum2363.graph fusedMap2133swap=true := by decide +kernel
theorem certified2133swap : Certified (graph core2133) (root 8) 4 0 :=
  of_native_maps core2133 DegreeTwoThreeSpectrum2770.graph DegreeTwoThreeSpectrum2363.graph
    sourceMap2133swap fusedMap2133swap sourceMap2133swap_checked fusedMap2133swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2133
#print axioms sourceMap2133swap_checked
#print axioms fusedMap2133swap_checked
#print axioms certified2133swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
