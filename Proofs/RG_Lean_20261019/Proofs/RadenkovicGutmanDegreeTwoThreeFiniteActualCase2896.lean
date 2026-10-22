/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2896 : Family 10 := level10.get ⟨1311,by decide⟩
def sourceMap2896 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2896 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2896_checked : acceptsGraphIso
    (source (graph core2896) (root 10) 0 4) DegreeTwoThreeSpectrum6608.graph sourceMap2896=true := by decide +kernel
theorem fusedMap2896_checked : acceptsGraphIso
    (fused (graph core2896) (root 10) 0 4) DegreeTwoThreeSpectrum6609.graph fusedMap2896=true := by decide +kernel
theorem certified2896 : Certified (graph core2896) (root 10) 0 4 :=
  of_native_maps core2896 DegreeTwoThreeSpectrum6608.graph DegreeTwoThreeSpectrum6609.graph
    sourceMap2896 fusedMap2896 sourceMap2896_checked fusedMap2896_checked
    DegreeTwoThreeFiniteComparisons.comparison2896
#print axioms sourceMap2896_checked
#print axioms fusedMap2896_checked
#print axioms certified2896
def sourceMap2896swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2896swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2896swap_checked : acceptsGraphIso
    (source (graph core2896) (root 10) 4 0) DegreeTwoThreeSpectrum6608.graph sourceMap2896swap=true := by decide +kernel
theorem fusedMap2896swap_checked : acceptsGraphIso
    (fused (graph core2896) (root 10) 4 0) DegreeTwoThreeSpectrum6609.graph fusedMap2896swap=true := by decide +kernel
theorem certified2896swap : Certified (graph core2896) (root 10) 4 0 :=
  of_native_maps core2896 DegreeTwoThreeSpectrum6608.graph DegreeTwoThreeSpectrum6609.graph
    sourceMap2896swap fusedMap2896swap sourceMap2896swap_checked fusedMap2896swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2896
#print axioms sourceMap2896swap_checked
#print axioms fusedMap2896swap_checked
#print axioms certified2896swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
