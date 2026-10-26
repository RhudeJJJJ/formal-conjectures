/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3936 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap3936 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3936 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3936_checked : acceptsGraphIso
    (source (graph core3936) (root 6) 1 5) DegreeTwoThreeSpectrum2780.graph sourceMap3936=true := by decide +kernel
theorem fusedMap3936_checked : acceptsGraphIso
    (fused (graph core3936) (root 6) 1 5) DegreeTwoThreeSpectrum2370.graph fusedMap3936=true := by decide +kernel
theorem certified3936 : Certified (graph core3936) (root 6) 1 5 :=
  of_native_maps core3936 DegreeTwoThreeSpectrum2780.graph DegreeTwoThreeSpectrum2370.graph
    sourceMap3936 fusedMap3936 sourceMap3936_checked fusedMap3936_checked
    DegreeTwoThreeFiniteComparisons.comparison3936
#print axioms sourceMap3936_checked
#print axioms fusedMap3936_checked
#print axioms certified3936
def sourceMap3936swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,14,7,8] (sourceLabel 6 5 1 v)
def fusedMap3936swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3936swap_checked : acceptsGraphIso
    (source (graph core3936) (root 6) 5 1) DegreeTwoThreeSpectrum2780.graph sourceMap3936swap=true := by decide +kernel
theorem fusedMap3936swap_checked : acceptsGraphIso
    (fused (graph core3936) (root 6) 5 1) DegreeTwoThreeSpectrum2370.graph fusedMap3936swap=true := by decide +kernel
theorem certified3936swap : Certified (graph core3936) (root 6) 5 1 :=
  of_native_maps core3936 DegreeTwoThreeSpectrum2780.graph DegreeTwoThreeSpectrum2370.graph
    sourceMap3936swap fusedMap3936swap sourceMap3936swap_checked fusedMap3936swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3936
#print axioms sourceMap3936swap_checked
#print axioms fusedMap3936swap_checked
#print axioms certified3936swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
