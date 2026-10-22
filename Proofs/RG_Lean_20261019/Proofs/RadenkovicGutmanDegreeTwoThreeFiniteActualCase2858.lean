/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2858 : Family 10 := level10.get ⟨1214,by decide⟩
def sourceMap2858 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2858 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2858_checked : acceptsGraphIso
    (source (graph core2858) (root 10) 0 4) DegreeTwoThreeSpectrum6402.graph sourceMap2858=true := by decide +kernel
theorem fusedMap2858_checked : acceptsGraphIso
    (fused (graph core2858) (root 10) 0 4) DegreeTwoThreeSpectrum6403.graph fusedMap2858=true := by decide +kernel
theorem certified2858 : Certified (graph core2858) (root 10) 0 4 :=
  of_native_maps core2858 DegreeTwoThreeSpectrum6402.graph DegreeTwoThreeSpectrum6403.graph
    sourceMap2858 fusedMap2858 sourceMap2858_checked fusedMap2858_checked
    DegreeTwoThreeFiniteComparisons.comparison2858
#print axioms sourceMap2858_checked
#print axioms fusedMap2858_checked
#print axioms certified2858
def sourceMap2858swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2858swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2858swap_checked : acceptsGraphIso
    (source (graph core2858) (root 10) 4 0) DegreeTwoThreeSpectrum6402.graph sourceMap2858swap=true := by decide +kernel
theorem fusedMap2858swap_checked : acceptsGraphIso
    (fused (graph core2858) (root 10) 4 0) DegreeTwoThreeSpectrum6403.graph fusedMap2858swap=true := by decide +kernel
theorem certified2858swap : Certified (graph core2858) (root 10) 4 0 :=
  of_native_maps core2858 DegreeTwoThreeSpectrum6402.graph DegreeTwoThreeSpectrum6403.graph
    sourceMap2858swap fusedMap2858swap sourceMap2858swap_checked fusedMap2858swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2858
#print axioms sourceMap2858swap_checked
#print axioms fusedMap2858swap_checked
#print axioms certified2858swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
