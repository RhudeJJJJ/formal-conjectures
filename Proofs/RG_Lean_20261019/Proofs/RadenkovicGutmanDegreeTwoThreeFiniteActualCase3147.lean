/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3147 : Family 8 := level8.get ⟨38,by decide⟩
def sourceMap3147 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3147 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3147_checked : acceptsGraphIso
    (source (graph core3147) (root 8) 0 5) DegreeTwoThreeSpectrum3913.graph sourceMap3147=true := by decide +kernel
theorem fusedMap3147_checked : acceptsGraphIso
    (fused (graph core3147) (root 8) 0 5) DegreeTwoThreeSpectrum3914.graph fusedMap3147=true := by decide +kernel
theorem certified3147 : Certified (graph core3147) (root 8) 0 5 :=
  of_native_maps core3147 DegreeTwoThreeSpectrum3913.graph DegreeTwoThreeSpectrum3914.graph
    sourceMap3147 fusedMap3147 sourceMap3147_checked fusedMap3147_checked
    DegreeTwoThreeFiniteComparisons.comparison3147
#print axioms sourceMap3147_checked
#print axioms fusedMap3147_checked
#print axioms certified3147
def sourceMap3147swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3147swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3147swap_checked : acceptsGraphIso
    (source (graph core3147) (root 8) 5 0) DegreeTwoThreeSpectrum3913.graph sourceMap3147swap=true := by decide +kernel
theorem fusedMap3147swap_checked : acceptsGraphIso
    (fused (graph core3147) (root 8) 5 0) DegreeTwoThreeSpectrum3914.graph fusedMap3147swap=true := by decide +kernel
theorem certified3147swap : Certified (graph core3147) (root 8) 5 0 :=
  of_native_maps core3147 DegreeTwoThreeSpectrum3913.graph DegreeTwoThreeSpectrum3914.graph
    sourceMap3147swap fusedMap3147swap sourceMap3147swap_checked fusedMap3147swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3147
#print axioms sourceMap3147swap_checked
#print axioms fusedMap3147swap_checked
#print axioms certified3147swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
