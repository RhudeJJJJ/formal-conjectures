/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2905 : Family 10 := level10.get ⟨1332,by decide⟩
def sourceMap2905 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2905 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2905_checked : acceptsGraphIso
    (source (graph core2905) (root 10) 0 4) DegreeTwoThreeSpectrum6645.graph sourceMap2905=true := by decide +kernel
theorem fusedMap2905_checked : acceptsGraphIso
    (fused (graph core2905) (root 10) 0 4) DegreeTwoThreeSpectrum6646.graph fusedMap2905=true := by decide +kernel
theorem certified2905 : Certified (graph core2905) (root 10) 0 4 :=
  of_native_maps core2905 DegreeTwoThreeSpectrum6645.graph DegreeTwoThreeSpectrum6646.graph
    sourceMap2905 fusedMap2905 sourceMap2905_checked fusedMap2905_checked
    DegreeTwoThreeFiniteComparisons.comparison2905
#print axioms sourceMap2905_checked
#print axioms fusedMap2905_checked
#print axioms certified2905
def sourceMap2905swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2905swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2905swap_checked : acceptsGraphIso
    (source (graph core2905) (root 10) 4 0) DegreeTwoThreeSpectrum6645.graph sourceMap2905swap=true := by decide +kernel
theorem fusedMap2905swap_checked : acceptsGraphIso
    (fused (graph core2905) (root 10) 4 0) DegreeTwoThreeSpectrum6646.graph fusedMap2905swap=true := by decide +kernel
theorem certified2905swap : Certified (graph core2905) (root 10) 4 0 :=
  of_native_maps core2905 DegreeTwoThreeSpectrum6645.graph DegreeTwoThreeSpectrum6646.graph
    sourceMap2905swap fusedMap2905swap sourceMap2905swap_checked fusedMap2905swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2905
#print axioms sourceMap2905swap_checked
#print axioms fusedMap2905swap_checked
#print axioms certified2905swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
