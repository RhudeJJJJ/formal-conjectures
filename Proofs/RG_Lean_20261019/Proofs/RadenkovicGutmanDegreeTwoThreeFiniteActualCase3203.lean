/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3203 : Family 8 := level8.get ⟨193,by decide⟩
def sourceMap3203 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3203 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3203_checked : acceptsGraphIso
    (source (graph core3203) (root 8) 0 5) DegreeTwoThreeSpectrum4189.graph sourceMap3203=true := by decide +kernel
theorem fusedMap3203_checked : acceptsGraphIso
    (fused (graph core3203) (root 8) 0 5) DegreeTwoThreeSpectrum4190.graph fusedMap3203=true := by decide +kernel
theorem certified3203 : Certified (graph core3203) (root 8) 0 5 :=
  of_native_maps core3203 DegreeTwoThreeSpectrum4189.graph DegreeTwoThreeSpectrum4190.graph
    sourceMap3203 fusedMap3203 sourceMap3203_checked fusedMap3203_checked
    DegreeTwoThreeFiniteComparisons.comparison3203
#print axioms sourceMap3203_checked
#print axioms fusedMap3203_checked
#print axioms certified3203
def sourceMap3203swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3203swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3203swap_checked : acceptsGraphIso
    (source (graph core3203) (root 8) 5 0) DegreeTwoThreeSpectrum4189.graph sourceMap3203swap=true := by decide +kernel
theorem fusedMap3203swap_checked : acceptsGraphIso
    (fused (graph core3203) (root 8) 5 0) DegreeTwoThreeSpectrum4190.graph fusedMap3203swap=true := by decide +kernel
theorem certified3203swap : Certified (graph core3203) (root 8) 5 0 :=
  of_native_maps core3203 DegreeTwoThreeSpectrum4189.graph DegreeTwoThreeSpectrum4190.graph
    sourceMap3203swap fusedMap3203swap sourceMap3203swap_checked fusedMap3203swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3203
#print axioms sourceMap3203swap_checked
#print axioms fusedMap3203swap_checked
#print axioms certified3203swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
