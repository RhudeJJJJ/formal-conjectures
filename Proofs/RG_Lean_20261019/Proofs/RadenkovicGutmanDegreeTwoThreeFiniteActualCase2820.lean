/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2820 : Family 10 := level10.get ⟨1128,by decide⟩
def sourceMap2820 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2820 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2820_checked : acceptsGraphIso
    (source (graph core2820) (root 10) 0 4) DegreeTwoThreeSpectrum6241.graph sourceMap2820=true := by decide +kernel
theorem fusedMap2820_checked : acceptsGraphIso
    (fused (graph core2820) (root 10) 0 4) DegreeTwoThreeSpectrum6242.graph fusedMap2820=true := by decide +kernel
theorem certified2820 : Certified (graph core2820) (root 10) 0 4 :=
  of_native_maps core2820 DegreeTwoThreeSpectrum6241.graph DegreeTwoThreeSpectrum6242.graph
    sourceMap2820 fusedMap2820 sourceMap2820_checked fusedMap2820_checked
    DegreeTwoThreeFiniteComparisons.comparison2820
#print axioms sourceMap2820_checked
#print axioms fusedMap2820_checked
#print axioms certified2820
def sourceMap2820swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2820swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2820swap_checked : acceptsGraphIso
    (source (graph core2820) (root 10) 4 0) DegreeTwoThreeSpectrum6241.graph sourceMap2820swap=true := by decide +kernel
theorem fusedMap2820swap_checked : acceptsGraphIso
    (fused (graph core2820) (root 10) 4 0) DegreeTwoThreeSpectrum6242.graph fusedMap2820swap=true := by decide +kernel
theorem certified2820swap : Certified (graph core2820) (root 10) 4 0 :=
  of_native_maps core2820 DegreeTwoThreeSpectrum6241.graph DegreeTwoThreeSpectrum6242.graph
    sourceMap2820swap fusedMap2820swap sourceMap2820swap_checked fusedMap2820swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2820
#print axioms sourceMap2820swap_checked
#print axioms fusedMap2820swap_checked
#print axioms certified2820swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
