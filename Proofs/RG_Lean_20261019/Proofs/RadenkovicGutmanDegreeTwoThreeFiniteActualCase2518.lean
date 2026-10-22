/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2518 : Family 10 := level10.get ⟨275,by decide⟩
def sourceMap2518 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2518 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2518_checked : acceptsGraphIso
    (source (graph core2518) (root 10) 0 4) DegreeTwoThreeSpectrum5405.graph sourceMap2518=true := by decide +kernel
theorem fusedMap2518_checked : acceptsGraphIso
    (fused (graph core2518) (root 10) 0 4) DegreeTwoThreeSpectrum5406.graph fusedMap2518=true := by decide +kernel
theorem certified2518 : Certified (graph core2518) (root 10) 0 4 :=
  of_native_maps core2518 DegreeTwoThreeSpectrum5405.graph DegreeTwoThreeSpectrum5406.graph
    sourceMap2518 fusedMap2518 sourceMap2518_checked fusedMap2518_checked
    DegreeTwoThreeFiniteComparisons.comparison2518
#print axioms sourceMap2518_checked
#print axioms fusedMap2518_checked
#print axioms certified2518
def sourceMap2518swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2518swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2518swap_checked : acceptsGraphIso
    (source (graph core2518) (root 10) 4 0) DegreeTwoThreeSpectrum5405.graph sourceMap2518swap=true := by decide +kernel
theorem fusedMap2518swap_checked : acceptsGraphIso
    (fused (graph core2518) (root 10) 4 0) DegreeTwoThreeSpectrum5406.graph fusedMap2518swap=true := by decide +kernel
theorem certified2518swap : Certified (graph core2518) (root 10) 4 0 :=
  of_native_maps core2518 DegreeTwoThreeSpectrum5405.graph DegreeTwoThreeSpectrum5406.graph
    sourceMap2518swap fusedMap2518swap sourceMap2518swap_checked fusedMap2518swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2518
#print axioms sourceMap2518swap_checked
#print axioms fusedMap2518swap_checked
#print axioms certified2518swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
