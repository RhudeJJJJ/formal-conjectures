/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3087 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap3087 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3087 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3087_checked : acceptsGraphIso
    (source (graph core3087) (root 6) 0 5) DegreeTwoThreeSpectrum1736.graph sourceMap3087=true := by decide +kernel
theorem fusedMap3087_checked : acceptsGraphIso
    (fused (graph core3087) (root 6) 0 5) DegreeTwoThreeSpectrum1737.graph fusedMap3087=true := by decide +kernel
theorem certified3087 : Certified (graph core3087) (root 6) 0 5 :=
  of_native_maps core3087 DegreeTwoThreeSpectrum1736.graph DegreeTwoThreeSpectrum1737.graph
    sourceMap3087 fusedMap3087 sourceMap3087_checked fusedMap3087_checked
    DegreeTwoThreeFiniteComparisons.comparison3087
#print axioms sourceMap3087_checked
#print axioms fusedMap3087_checked
#print axioms certified3087
def sourceMap3087swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,12,13,7] (sourceLabel 6 5 0 v)
def fusedMap3087swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3087swap_checked : acceptsGraphIso
    (source (graph core3087) (root 6) 5 0) DegreeTwoThreeSpectrum1736.graph sourceMap3087swap=true := by decide +kernel
theorem fusedMap3087swap_checked : acceptsGraphIso
    (fused (graph core3087) (root 6) 5 0) DegreeTwoThreeSpectrum1737.graph fusedMap3087swap=true := by decide +kernel
theorem certified3087swap : Certified (graph core3087) (root 6) 5 0 :=
  of_native_maps core3087 DegreeTwoThreeSpectrum1736.graph DegreeTwoThreeSpectrum1737.graph
    sourceMap3087swap fusedMap3087swap sourceMap3087swap_checked fusedMap3087swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3087
#print axioms sourceMap3087swap_checked
#print axioms fusedMap3087swap_checked
#print axioms certified3087swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
