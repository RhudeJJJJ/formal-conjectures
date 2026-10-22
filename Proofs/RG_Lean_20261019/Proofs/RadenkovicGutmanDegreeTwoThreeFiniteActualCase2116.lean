/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2116 : Family 7 := level7.get ⟨101,by decide⟩
def sourceMap2116 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2116 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2116_checked : acceptsGraphIso
    (source (graph core2116) (root 7) 0 4) DegreeTwoThreeSpectrum1926.graph sourceMap2116=true := by decide +kernel
theorem fusedMap2116_checked : acceptsGraphIso
    (fused (graph core2116) (root 7) 0 4) DegreeTwoThreeSpectrum1928.graph fusedMap2116=true := by decide +kernel
theorem certified2116 : Certified (graph core2116) (root 7) 0 4 :=
  of_native_maps core2116 DegreeTwoThreeSpectrum1926.graph DegreeTwoThreeSpectrum1928.graph
    sourceMap2116 fusedMap2116 sourceMap2116_checked fusedMap2116_checked
    DegreeTwoThreeFiniteComparisons.comparison2116
#print axioms sourceMap2116_checked
#print axioms fusedMap2116_checked
#print axioms certified2116
def sourceMap2116swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2116swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2116swap_checked : acceptsGraphIso
    (source (graph core2116) (root 7) 4 0) DegreeTwoThreeSpectrum1926.graph sourceMap2116swap=true := by decide +kernel
theorem fusedMap2116swap_checked : acceptsGraphIso
    (fused (graph core2116) (root 7) 4 0) DegreeTwoThreeSpectrum1928.graph fusedMap2116swap=true := by decide +kernel
theorem certified2116swap : Certified (graph core2116) (root 7) 4 0 :=
  of_native_maps core2116 DegreeTwoThreeSpectrum1926.graph DegreeTwoThreeSpectrum1928.graph
    sourceMap2116swap fusedMap2116swap sourceMap2116swap_checked fusedMap2116swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2116
#print axioms sourceMap2116swap_checked
#print axioms fusedMap2116swap_checked
#print axioms certified2116swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
