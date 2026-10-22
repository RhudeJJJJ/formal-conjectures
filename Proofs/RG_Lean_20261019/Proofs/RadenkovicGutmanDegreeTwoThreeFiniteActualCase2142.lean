/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2142 : Family 8 := level8.get ⟨89,by decide⟩
def sourceMap2142 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11] (sourceLabel 8 0 4 v)
def fusedMap2142 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2142_checked : acceptsGraphIso
    (source (graph core2142) (root 8) 0 4) DegreeTwoThreeSpectrum2991.graph sourceMap2142=true := by decide +kernel
theorem fusedMap2142_checked : acceptsGraphIso
    (fused (graph core2142) (root 8) 0 4) DegreeTwoThreeSpectrum2418.graph fusedMap2142=true := by decide +kernel
theorem certified2142 : Certified (graph core2142) (root 8) 0 4 :=
  of_native_maps core2142 DegreeTwoThreeSpectrum2991.graph DegreeTwoThreeSpectrum2418.graph
    sourceMap2142 fusedMap2142 sourceMap2142_checked fusedMap2142_checked
    DegreeTwoThreeFiniteComparisons.comparison2142
#print axioms sourceMap2142_checked
#print axioms fusedMap2142_checked
#print axioms certified2142
def sourceMap2142swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,12,13,7,8,9,10,11,14] (sourceLabel 8 4 0 v)
def fusedMap2142swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2142swap_checked : acceptsGraphIso
    (source (graph core2142) (root 8) 4 0) DegreeTwoThreeSpectrum2991.graph sourceMap2142swap=true := by decide +kernel
theorem fusedMap2142swap_checked : acceptsGraphIso
    (fused (graph core2142) (root 8) 4 0) DegreeTwoThreeSpectrum2418.graph fusedMap2142swap=true := by decide +kernel
theorem certified2142swap : Certified (graph core2142) (root 8) 4 0 :=
  of_native_maps core2142 DegreeTwoThreeSpectrum2991.graph DegreeTwoThreeSpectrum2418.graph
    sourceMap2142swap fusedMap2142swap sourceMap2142swap_checked fusedMap2142swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2142
#print axioms sourceMap2142swap_checked
#print axioms fusedMap2142swap_checked
#print axioms certified2142swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
