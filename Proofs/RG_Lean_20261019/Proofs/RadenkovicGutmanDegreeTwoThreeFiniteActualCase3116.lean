/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3116 : Family 7 := level7.get ⟨48,by decide⟩
def sourceMap3116 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3116 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3116_checked : acceptsGraphIso
    (source (graph core3116) (root 7) 0 5) DegreeTwoThreeSpectrum2780.graph sourceMap3116=true := by decide +kernel
theorem fusedMap3116_checked : acceptsGraphIso
    (fused (graph core3116) (root 7) 0 5) DegreeTwoThreeSpectrum2366.graph fusedMap3116=true := by decide +kernel
theorem certified3116 : Certified (graph core3116) (root 7) 0 5 :=
  of_native_maps core3116 DegreeTwoThreeSpectrum2780.graph DegreeTwoThreeSpectrum2366.graph
    sourceMap3116 fusedMap3116 sourceMap3116_checked fusedMap3116_checked
    DegreeTwoThreeFiniteComparisons.comparison3116
#print axioms sourceMap3116_checked
#print axioms fusedMap3116_checked
#print axioms certified3116
def sourceMap3116swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3116swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3116swap_checked : acceptsGraphIso
    (source (graph core3116) (root 7) 5 0) DegreeTwoThreeSpectrum2780.graph sourceMap3116swap=true := by decide +kernel
theorem fusedMap3116swap_checked : acceptsGraphIso
    (fused (graph core3116) (root 7) 5 0) DegreeTwoThreeSpectrum2366.graph fusedMap3116swap=true := by decide +kernel
theorem certified3116swap : Certified (graph core3116) (root 7) 5 0 :=
  of_native_maps core3116 DegreeTwoThreeSpectrum2780.graph DegreeTwoThreeSpectrum2366.graph
    sourceMap3116swap fusedMap3116swap sourceMap3116swap_checked fusedMap3116swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3116
#print axioms sourceMap3116swap_checked
#print axioms fusedMap3116swap_checked
#print axioms certified3116swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
