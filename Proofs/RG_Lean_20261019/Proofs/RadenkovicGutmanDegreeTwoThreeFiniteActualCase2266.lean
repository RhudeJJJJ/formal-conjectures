/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2266 : Family 9 := level9.get ⟨195,by decide⟩
def sourceMap2266 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11] (sourceLabel 9 0 4 v)
def fusedMap2266 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2266_checked : acceptsGraphIso
    (source (graph core2266) (root 9) 0 4) DegreeTwoThreeSpectrum4388.graph sourceMap2266=true := by decide +kernel
theorem fusedMap2266_checked : acceptsGraphIso
    (fused (graph core2266) (root 9) 0 4) DegreeTwoThreeSpectrum3971.graph fusedMap2266=true := by decide +kernel
theorem certified2266 : Certified (graph core2266) (root 9) 0 4 :=
  of_native_maps core2266 DegreeTwoThreeSpectrum4388.graph DegreeTwoThreeSpectrum3971.graph
    sourceMap2266 fusedMap2266 sourceMap2266_checked fusedMap2266_checked
    DegreeTwoThreeFiniteComparisons.comparison2266
#print axioms sourceMap2266_checked
#print axioms fusedMap2266_checked
#print axioms certified2266
def sourceMap2266swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11,15] (sourceLabel 9 4 0 v)
def fusedMap2266swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2266swap_checked : acceptsGraphIso
    (source (graph core2266) (root 9) 4 0) DegreeTwoThreeSpectrum4388.graph sourceMap2266swap=true := by decide +kernel
theorem fusedMap2266swap_checked : acceptsGraphIso
    (fused (graph core2266) (root 9) 4 0) DegreeTwoThreeSpectrum3971.graph fusedMap2266swap=true := by decide +kernel
theorem certified2266swap : Certified (graph core2266) (root 9) 4 0 :=
  of_native_maps core2266 DegreeTwoThreeSpectrum4388.graph DegreeTwoThreeSpectrum3971.graph
    sourceMap2266swap fusedMap2266swap sourceMap2266swap_checked fusedMap2266swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2266
#print axioms sourceMap2266swap_checked
#print axioms fusedMap2266swap_checked
#print axioms certified2266swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
