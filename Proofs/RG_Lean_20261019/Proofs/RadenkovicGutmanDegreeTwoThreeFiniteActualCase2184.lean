/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2184 : Family 8 := level8.get ⟨198,by decide⟩
def sourceMap2184 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2184 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2184_checked : acceptsGraphIso
    (source (graph core2184) (root 8) 0 4) DegreeTwoThreeSpectrum3076.graph sourceMap2184=true := by decide +kernel
theorem fusedMap2184_checked : acceptsGraphIso
    (fused (graph core2184) (root 8) 0 4) DegreeTwoThreeSpectrum2457.graph fusedMap2184=true := by decide +kernel
theorem certified2184 : Certified (graph core2184) (root 8) 0 4 :=
  of_native_maps core2184 DegreeTwoThreeSpectrum3076.graph DegreeTwoThreeSpectrum2457.graph
    sourceMap2184 fusedMap2184 sourceMap2184_checked fusedMap2184_checked
    DegreeTwoThreeFiniteComparisons.comparison2184
#print axioms sourceMap2184_checked
#print axioms fusedMap2184_checked
#print axioms certified2184
def sourceMap2184swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2184swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2184swap_checked : acceptsGraphIso
    (source (graph core2184) (root 8) 4 0) DegreeTwoThreeSpectrum3076.graph sourceMap2184swap=true := by decide +kernel
theorem fusedMap2184swap_checked : acceptsGraphIso
    (fused (graph core2184) (root 8) 4 0) DegreeTwoThreeSpectrum2457.graph fusedMap2184swap=true := by decide +kernel
theorem certified2184swap : Certified (graph core2184) (root 8) 4 0 :=
  of_native_maps core2184 DegreeTwoThreeSpectrum3076.graph DegreeTwoThreeSpectrum2457.graph
    sourceMap2184swap fusedMap2184swap sourceMap2184swap_checked fusedMap2184swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2184
#print axioms sourceMap2184swap_checked
#print axioms fusedMap2184swap_checked
#print axioms certified2184swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
