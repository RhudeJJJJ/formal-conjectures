/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2416 : Family 9 := level9.get ⟨580,by decide⟩
def sourceMap2416 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2416 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2416_checked : acceptsGraphIso
    (source (graph core2416) (root 9) 0 4) DegreeTwoThreeSpectrum4712.graph sourceMap2416=true := by decide +kernel
theorem fusedMap2416_checked : acceptsGraphIso
    (fused (graph core2416) (root 9) 0 4) DegreeTwoThreeSpectrum4237.graph fusedMap2416=true := by decide +kernel
theorem certified2416 : Certified (graph core2416) (root 9) 0 4 :=
  of_native_maps core2416 DegreeTwoThreeSpectrum4712.graph DegreeTwoThreeSpectrum4237.graph
    sourceMap2416 fusedMap2416 sourceMap2416_checked fusedMap2416_checked
    DegreeTwoThreeFiniteComparisons.comparison2416
#print axioms sourceMap2416_checked
#print axioms fusedMap2416_checked
#print axioms certified2416
def sourceMap2416swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2416swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2416swap_checked : acceptsGraphIso
    (source (graph core2416) (root 9) 4 0) DegreeTwoThreeSpectrum4712.graph sourceMap2416swap=true := by decide +kernel
theorem fusedMap2416swap_checked : acceptsGraphIso
    (fused (graph core2416) (root 9) 4 0) DegreeTwoThreeSpectrum4237.graph fusedMap2416swap=true := by decide +kernel
theorem certified2416swap : Certified (graph core2416) (root 9) 4 0 :=
  of_native_maps core2416 DegreeTwoThreeSpectrum4712.graph DegreeTwoThreeSpectrum4237.graph
    sourceMap2416swap fusedMap2416swap sourceMap2416swap_checked fusedMap2416swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2416
#print axioms sourceMap2416swap_checked
#print axioms fusedMap2416swap_checked
#print axioms certified2416swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
