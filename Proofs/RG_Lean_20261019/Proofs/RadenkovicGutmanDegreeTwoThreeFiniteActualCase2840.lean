/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2840 : Family 10 := level10.get ⟨1176,by decide⟩
def sourceMap2840 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2840 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2840_checked : acceptsGraphIso
    (source (graph core2840) (root 10) 0 4) DegreeTwoThreeSpectrum6336.graph sourceMap2840=true := by decide +kernel
theorem fusedMap2840_checked : acceptsGraphIso
    (fused (graph core2840) (root 10) 0 4) DegreeTwoThreeSpectrum6337.graph fusedMap2840=true := by decide +kernel
theorem certified2840 : Certified (graph core2840) (root 10) 0 4 :=
  of_native_maps core2840 DegreeTwoThreeSpectrum6336.graph DegreeTwoThreeSpectrum6337.graph
    sourceMap2840 fusedMap2840 sourceMap2840_checked fusedMap2840_checked
    DegreeTwoThreeFiniteComparisons.comparison2840
#print axioms sourceMap2840_checked
#print axioms fusedMap2840_checked
#print axioms certified2840
def sourceMap2840swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2840swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2840swap_checked : acceptsGraphIso
    (source (graph core2840) (root 10) 4 0) DegreeTwoThreeSpectrum6336.graph sourceMap2840swap=true := by decide +kernel
theorem fusedMap2840swap_checked : acceptsGraphIso
    (fused (graph core2840) (root 10) 4 0) DegreeTwoThreeSpectrum6337.graph fusedMap2840swap=true := by decide +kernel
theorem certified2840swap : Certified (graph core2840) (root 10) 4 0 :=
  of_native_maps core2840 DegreeTwoThreeSpectrum6336.graph DegreeTwoThreeSpectrum6337.graph
    sourceMap2840swap fusedMap2840swap sourceMap2840swap_checked fusedMap2840swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2840
#print axioms sourceMap2840swap_checked
#print axioms fusedMap2840swap_checked
#print axioms certified2840swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
