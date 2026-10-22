/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2973 : Family 10 := level10.get ⟨1485,by decide⟩
def sourceMap2973 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2973 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2973_checked : acceptsGraphIso
    (source (graph core2973) (root 10) 0 4) DegreeTwoThreeSpectrum6977.graph sourceMap2973=true := by decide +kernel
theorem fusedMap2973_checked : acceptsGraphIso
    (fused (graph core2973) (root 10) 0 4) DegreeTwoThreeSpectrum6978.graph fusedMap2973=true := by decide +kernel
theorem certified2973 : Certified (graph core2973) (root 10) 0 4 :=
  of_native_maps core2973 DegreeTwoThreeSpectrum6977.graph DegreeTwoThreeSpectrum6978.graph
    sourceMap2973 fusedMap2973 sourceMap2973_checked fusedMap2973_checked
    DegreeTwoThreeFiniteComparisons.comparison2973
#print axioms sourceMap2973_checked
#print axioms fusedMap2973_checked
#print axioms certified2973
def sourceMap2973swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2973swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2973swap_checked : acceptsGraphIso
    (source (graph core2973) (root 10) 4 0) DegreeTwoThreeSpectrum6977.graph sourceMap2973swap=true := by decide +kernel
theorem fusedMap2973swap_checked : acceptsGraphIso
    (fused (graph core2973) (root 10) 4 0) DegreeTwoThreeSpectrum6978.graph fusedMap2973swap=true := by decide +kernel
theorem certified2973swap : Certified (graph core2973) (root 10) 4 0 :=
  of_native_maps core2973 DegreeTwoThreeSpectrum6977.graph DegreeTwoThreeSpectrum6978.graph
    sourceMap2973swap fusedMap2973swap sourceMap2973swap_checked fusedMap2973swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2973
#print axioms sourceMap2973swap_checked
#print axioms fusedMap2973swap_checked
#print axioms certified2973swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
