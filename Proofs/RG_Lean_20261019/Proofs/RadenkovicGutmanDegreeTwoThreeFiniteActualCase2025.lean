/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2025 : Family 10 := level10.get ⟨1702,by decide⟩
def sourceMap2025 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap2025 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2025_checked : acceptsGraphIso
    (source (graph core2025) (root 10) 0 2) DegreeTwoThreeSpectrum3819.graph sourceMap2025=true := by decide +kernel
theorem fusedMap2025_checked : acceptsGraphIso
    (fused (graph core2025) (root 10) 0 2) DegreeTwoThreeSpectrum3377.graph fusedMap2025=true := by decide +kernel
theorem certified2025 : Certified (graph core2025) (root 10) 0 2 :=
  of_native_maps core2025 DegreeTwoThreeSpectrum3819.graph DegreeTwoThreeSpectrum3377.graph
    sourceMap2025 fusedMap2025 sourceMap2025_checked fusedMap2025_checked
    DegreeTwoThreeFiniteComparisons.comparison2025
#print axioms sourceMap2025_checked
#print axioms fusedMap2025_checked
#print axioms certified2025
def sourceMap2025swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap2025swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2025swap_checked : acceptsGraphIso
    (source (graph core2025) (root 10) 2 0) DegreeTwoThreeSpectrum3819.graph sourceMap2025swap=true := by decide +kernel
theorem fusedMap2025swap_checked : acceptsGraphIso
    (fused (graph core2025) (root 10) 2 0) DegreeTwoThreeSpectrum3377.graph fusedMap2025swap=true := by decide +kernel
theorem certified2025swap : Certified (graph core2025) (root 10) 2 0 :=
  of_native_maps core2025 DegreeTwoThreeSpectrum3819.graph DegreeTwoThreeSpectrum3377.graph
    sourceMap2025swap fusedMap2025swap sourceMap2025swap_checked fusedMap2025swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2025
#print axioms sourceMap2025swap_checked
#print axioms fusedMap2025swap_checked
#print axioms certified2025swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
