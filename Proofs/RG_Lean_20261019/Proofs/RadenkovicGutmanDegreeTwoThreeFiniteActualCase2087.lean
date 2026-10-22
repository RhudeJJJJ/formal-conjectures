/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2087 : Family 7 := level7.get ⟨24,by decide⟩
def sourceMap2087 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,11,12,13,6,7,8,9,10] (sourceLabel 7 0 4 v)
def fusedMap2087 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2087_checked : acceptsGraphIso
    (source (graph core2087) (root 7) 0 4) DegreeTwoThreeSpectrum1924.graph sourceMap2087=true := by decide +kernel
theorem fusedMap2087_checked : acceptsGraphIso
    (fused (graph core2087) (root 7) 0 4) DegreeTwoThreeSpectrum1735.graph fusedMap2087=true := by decide +kernel
theorem certified2087 : Certified (graph core2087) (root 7) 0 4 :=
  of_native_maps core2087 DegreeTwoThreeSpectrum1924.graph DegreeTwoThreeSpectrum1735.graph
    sourceMap2087 fusedMap2087 sourceMap2087_checked fusedMap2087_checked
    DegreeTwoThreeFiniteComparisons.comparison2087
#print axioms sourceMap2087_checked
#print axioms fusedMap2087_checked
#print axioms certified2087
def sourceMap2087swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,11,12,6,7,8,9,10,13] (sourceLabel 7 4 0 v)
def fusedMap2087swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2087swap_checked : acceptsGraphIso
    (source (graph core2087) (root 7) 4 0) DegreeTwoThreeSpectrum1924.graph sourceMap2087swap=true := by decide +kernel
theorem fusedMap2087swap_checked : acceptsGraphIso
    (fused (graph core2087) (root 7) 4 0) DegreeTwoThreeSpectrum1735.graph fusedMap2087swap=true := by decide +kernel
theorem certified2087swap : Certified (graph core2087) (root 7) 4 0 :=
  of_native_maps core2087 DegreeTwoThreeSpectrum1924.graph DegreeTwoThreeSpectrum1735.graph
    sourceMap2087swap fusedMap2087swap sourceMap2087swap_checked fusedMap2087swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2087
#print axioms sourceMap2087swap_checked
#print axioms fusedMap2087swap_checked
#print axioms certified2087swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
