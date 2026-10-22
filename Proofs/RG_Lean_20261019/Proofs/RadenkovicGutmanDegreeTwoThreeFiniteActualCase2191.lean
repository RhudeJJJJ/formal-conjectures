/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2191 : Family 8 := level8.get ⟨212,by decide⟩
def sourceMap2191 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2191 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2191_checked : acceptsGraphIso
    (source (graph core2191) (root 8) 0 4) DegreeTwoThreeSpectrum3191.graph sourceMap2191=true := by decide +kernel
theorem fusedMap2191_checked : acceptsGraphIso
    (fused (graph core2191) (root 8) 0 4) DegreeTwoThreeSpectrum2510.graph fusedMap2191=true := by decide +kernel
theorem certified2191 : Certified (graph core2191) (root 8) 0 4 :=
  of_native_maps core2191 DegreeTwoThreeSpectrum3191.graph DegreeTwoThreeSpectrum2510.graph
    sourceMap2191 fusedMap2191 sourceMap2191_checked fusedMap2191_checked
    DegreeTwoThreeFiniteComparisons.comparison2191
#print axioms sourceMap2191_checked
#print axioms fusedMap2191_checked
#print axioms certified2191
def sourceMap2191swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2191swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2191swap_checked : acceptsGraphIso
    (source (graph core2191) (root 8) 4 0) DegreeTwoThreeSpectrum3191.graph sourceMap2191swap=true := by decide +kernel
theorem fusedMap2191swap_checked : acceptsGraphIso
    (fused (graph core2191) (root 8) 4 0) DegreeTwoThreeSpectrum2510.graph fusedMap2191swap=true := by decide +kernel
theorem certified2191swap : Certified (graph core2191) (root 8) 4 0 :=
  of_native_maps core2191 DegreeTwoThreeSpectrum3191.graph DegreeTwoThreeSpectrum2510.graph
    sourceMap2191swap fusedMap2191swap sourceMap2191swap_checked fusedMap2191swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2191
#print axioms sourceMap2191swap_checked
#print axioms fusedMap2191swap_checked
#print axioms certified2191swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
