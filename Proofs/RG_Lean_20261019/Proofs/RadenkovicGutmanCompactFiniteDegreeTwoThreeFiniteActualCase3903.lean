/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3903 : Family 8 := level8.get ⟨219,by decide⟩
def sourceMap3903 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3903 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3903_checked : acceptsGraphIso
    (source (graph core3903) (root 8) 1 4) DegreeTwoThreeSpectrum4749.graph sourceMap3903=true := by decide +kernel
theorem fusedMap3903_checked : acceptsGraphIso
    (fused (graph core3903) (root 8) 1 4) DegreeTwoThreeSpectrum4309.graph fusedMap3903=true := by decide +kernel
theorem certified3903 : Certified (graph core3903) (root 8) 1 4 :=
  of_native_maps core3903 DegreeTwoThreeSpectrum4749.graph DegreeTwoThreeSpectrum4309.graph
    sourceMap3903 fusedMap3903 sourceMap3903_checked fusedMap3903_checked
    DegreeTwoThreeFiniteComparisons.comparison3903
#print axioms sourceMap3903_checked
#print axioms fusedMap3903_checked
#print axioms certified3903
def sourceMap3903swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3903swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3903swap_checked : acceptsGraphIso
    (source (graph core3903) (root 8) 4 1) DegreeTwoThreeSpectrum4749.graph sourceMap3903swap=true := by decide +kernel
theorem fusedMap3903swap_checked : acceptsGraphIso
    (fused (graph core3903) (root 8) 4 1) DegreeTwoThreeSpectrum4309.graph fusedMap3903swap=true := by decide +kernel
theorem certified3903swap : Certified (graph core3903) (root 8) 4 1 :=
  of_native_maps core3903 DegreeTwoThreeSpectrum4749.graph DegreeTwoThreeSpectrum4309.graph
    sourceMap3903swap fusedMap3903swap sourceMap3903swap_checked fusedMap3903swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3903
#print axioms sourceMap3903swap_checked
#print axioms fusedMap3903swap_checked
#print axioms certified3903swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
