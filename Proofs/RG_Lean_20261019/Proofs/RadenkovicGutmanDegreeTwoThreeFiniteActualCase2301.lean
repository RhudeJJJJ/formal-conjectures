/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2301 : Family 9 := level9.get ⟨298,by decide⟩
def sourceMap2301 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2301 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2301_checked : acceptsGraphIso
    (source (graph core2301) (root 9) 0 4) DegreeTwoThreeSpectrum4652.graph sourceMap2301=true := by decide +kernel
theorem fusedMap2301_checked : acceptsGraphIso
    (fused (graph core2301) (root 9) 0 4) DegreeTwoThreeSpectrum4128.graph fusedMap2301=true := by decide +kernel
theorem certified2301 : Certified (graph core2301) (root 9) 0 4 :=
  of_native_maps core2301 DegreeTwoThreeSpectrum4652.graph DegreeTwoThreeSpectrum4128.graph
    sourceMap2301 fusedMap2301 sourceMap2301_checked fusedMap2301_checked
    DegreeTwoThreeFiniteComparisons.comparison2301
#print axioms sourceMap2301_checked
#print axioms fusedMap2301_checked
#print axioms certified2301
def sourceMap2301swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2301swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2301swap_checked : acceptsGraphIso
    (source (graph core2301) (root 9) 4 0) DegreeTwoThreeSpectrum4652.graph sourceMap2301swap=true := by decide +kernel
theorem fusedMap2301swap_checked : acceptsGraphIso
    (fused (graph core2301) (root 9) 4 0) DegreeTwoThreeSpectrum4128.graph fusedMap2301swap=true := by decide +kernel
theorem certified2301swap : Certified (graph core2301) (root 9) 4 0 :=
  of_native_maps core2301 DegreeTwoThreeSpectrum4652.graph DegreeTwoThreeSpectrum4128.graph
    sourceMap2301swap fusedMap2301swap sourceMap2301swap_checked fusedMap2301swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2301
#print axioms sourceMap2301swap_checked
#print axioms fusedMap2301swap_checked
#print axioms certified2301swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
