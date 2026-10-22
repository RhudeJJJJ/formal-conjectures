/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2419 : Family 9 := level9.get ⟨591,by decide⟩
def sourceMap2419 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2419 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2419_checked : acceptsGraphIso
    (source (graph core2419) (root 9) 0 4) DegreeTwoThreeSpectrum4725.graph sourceMap2419=true := by decide +kernel
theorem fusedMap2419_checked : acceptsGraphIso
    (fused (graph core2419) (root 9) 0 4) DegreeTwoThreeSpectrum4267.graph fusedMap2419=true := by decide +kernel
theorem certified2419 : Certified (graph core2419) (root 9) 0 4 :=
  of_native_maps core2419 DegreeTwoThreeSpectrum4725.graph DegreeTwoThreeSpectrum4267.graph
    sourceMap2419 fusedMap2419 sourceMap2419_checked fusedMap2419_checked
    DegreeTwoThreeFiniteComparisons.comparison2419
#print axioms sourceMap2419_checked
#print axioms fusedMap2419_checked
#print axioms certified2419
def sourceMap2419swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2419swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2419swap_checked : acceptsGraphIso
    (source (graph core2419) (root 9) 4 0) DegreeTwoThreeSpectrum4725.graph sourceMap2419swap=true := by decide +kernel
theorem fusedMap2419swap_checked : acceptsGraphIso
    (fused (graph core2419) (root 9) 4 0) DegreeTwoThreeSpectrum4267.graph fusedMap2419swap=true := by decide +kernel
theorem certified2419swap : Certified (graph core2419) (root 9) 4 0 :=
  of_native_maps core2419 DegreeTwoThreeSpectrum4725.graph DegreeTwoThreeSpectrum4267.graph
    sourceMap2419swap fusedMap2419swap sourceMap2419swap_checked fusedMap2419swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2419
#print axioms sourceMap2419swap_checked
#print axioms fusedMap2419swap_checked
#print axioms certified2419swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
