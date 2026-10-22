/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2118 : Family 7 := level7.get ⟨104,by decide⟩
def sourceMap2118 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2118 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2118_checked : acceptsGraphIso
    (source (graph core2118) (root 7) 0 4) DegreeTwoThreeSpectrum1948.graph sourceMap2118=true := by decide +kernel
theorem fusedMap2118_checked : acceptsGraphIso
    (fused (graph core2118) (root 7) 0 4) DegreeTwoThreeSpectrum1950.graph fusedMap2118=true := by decide +kernel
theorem certified2118 : Certified (graph core2118) (root 7) 0 4 :=
  of_native_maps core2118 DegreeTwoThreeSpectrum1948.graph DegreeTwoThreeSpectrum1950.graph
    sourceMap2118 fusedMap2118 sourceMap2118_checked fusedMap2118_checked
    DegreeTwoThreeFiniteComparisons.comparison2118
#print axioms sourceMap2118_checked
#print axioms fusedMap2118_checked
#print axioms certified2118
def sourceMap2118swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2118swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2118swap_checked : acceptsGraphIso
    (source (graph core2118) (root 7) 4 0) DegreeTwoThreeSpectrum1948.graph sourceMap2118swap=true := by decide +kernel
theorem fusedMap2118swap_checked : acceptsGraphIso
    (fused (graph core2118) (root 7) 4 0) DegreeTwoThreeSpectrum1950.graph fusedMap2118swap=true := by decide +kernel
theorem certified2118swap : Certified (graph core2118) (root 7) 4 0 :=
  of_native_maps core2118 DegreeTwoThreeSpectrum1948.graph DegreeTwoThreeSpectrum1950.graph
    sourceMap2118swap fusedMap2118swap sourceMap2118swap_checked fusedMap2118swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2118
#print axioms sourceMap2118swap_checked
#print axioms fusedMap2118swap_checked
#print axioms certified2118swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
