/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2814 : Family 10 := level10.get ⟨1112,by decide⟩
def sourceMap2814 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2814 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2814_checked : acceptsGraphIso
    (source (graph core2814) (root 10) 0 4) DegreeTwoThreeSpectrum6209.graph sourceMap2814=true := by decide +kernel
theorem fusedMap2814_checked : acceptsGraphIso
    (fused (graph core2814) (root 10) 0 4) DegreeTwoThreeSpectrum6210.graph fusedMap2814=true := by decide +kernel
theorem certified2814 : Certified (graph core2814) (root 10) 0 4 :=
  of_native_maps core2814 DegreeTwoThreeSpectrum6209.graph DegreeTwoThreeSpectrum6210.graph
    sourceMap2814 fusedMap2814 sourceMap2814_checked fusedMap2814_checked
    DegreeTwoThreeFiniteComparisons.comparison2814
#print axioms sourceMap2814_checked
#print axioms fusedMap2814_checked
#print axioms certified2814
def sourceMap2814swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2814swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2814swap_checked : acceptsGraphIso
    (source (graph core2814) (root 10) 4 0) DegreeTwoThreeSpectrum6209.graph sourceMap2814swap=true := by decide +kernel
theorem fusedMap2814swap_checked : acceptsGraphIso
    (fused (graph core2814) (root 10) 4 0) DegreeTwoThreeSpectrum6210.graph fusedMap2814swap=true := by decide +kernel
theorem certified2814swap : Certified (graph core2814) (root 10) 4 0 :=
  of_native_maps core2814 DegreeTwoThreeSpectrum6209.graph DegreeTwoThreeSpectrum6210.graph
    sourceMap2814swap fusedMap2814swap sourceMap2814swap_checked fusedMap2814swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2814
#print axioms sourceMap2814swap_checked
#print axioms fusedMap2814swap_checked
#print axioms certified2814swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
