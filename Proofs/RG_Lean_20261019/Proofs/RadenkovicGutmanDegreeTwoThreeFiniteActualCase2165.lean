/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2165 : Family 8 := level8.get ⟨154,by decide⟩
def sourceMap2165 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2165 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2165_checked : acceptsGraphIso
    (source (graph core2165) (root 8) 0 4) DegreeTwoThreeSpectrum2749.graph sourceMap2165=true := by decide +kernel
theorem fusedMap2165_checked : acceptsGraphIso
    (fused (graph core2165) (root 8) 0 4) DegreeTwoThreeSpectrum2751.graph fusedMap2165=true := by decide +kernel
theorem certified2165 : Certified (graph core2165) (root 8) 0 4 :=
  of_native_maps core2165 DegreeTwoThreeSpectrum2749.graph DegreeTwoThreeSpectrum2751.graph
    sourceMap2165 fusedMap2165 sourceMap2165_checked fusedMap2165_checked
    DegreeTwoThreeFiniteComparisons.comparison2165
#print axioms sourceMap2165_checked
#print axioms fusedMap2165_checked
#print axioms certified2165
def sourceMap2165swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2165swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2165swap_checked : acceptsGraphIso
    (source (graph core2165) (root 8) 4 0) DegreeTwoThreeSpectrum2749.graph sourceMap2165swap=true := by decide +kernel
theorem fusedMap2165swap_checked : acceptsGraphIso
    (fused (graph core2165) (root 8) 4 0) DegreeTwoThreeSpectrum2751.graph fusedMap2165swap=true := by decide +kernel
theorem certified2165swap : Certified (graph core2165) (root 8) 4 0 :=
  of_native_maps core2165 DegreeTwoThreeSpectrum2749.graph DegreeTwoThreeSpectrum2751.graph
    sourceMap2165swap fusedMap2165swap sourceMap2165swap_checked fusedMap2165swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2165
#print axioms sourceMap2165swap_checked
#print axioms fusedMap2165swap_checked
#print axioms certified2165swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
