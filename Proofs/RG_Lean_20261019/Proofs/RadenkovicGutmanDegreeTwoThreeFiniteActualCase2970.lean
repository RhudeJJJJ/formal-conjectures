/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2970 : Family 10 := level10.get ⟨1478,by decide⟩
def sourceMap2970 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2970 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2970_checked : acceptsGraphIso
    (source (graph core2970) (root 10) 0 4) DegreeTwoThreeSpectrum6965.graph sourceMap2970=true := by decide +kernel
theorem fusedMap2970_checked : acceptsGraphIso
    (fused (graph core2970) (root 10) 0 4) DegreeTwoThreeSpectrum6966.graph fusedMap2970=true := by decide +kernel
theorem certified2970 : Certified (graph core2970) (root 10) 0 4 :=
  of_native_maps core2970 DegreeTwoThreeSpectrum6965.graph DegreeTwoThreeSpectrum6966.graph
    sourceMap2970 fusedMap2970 sourceMap2970_checked fusedMap2970_checked
    DegreeTwoThreeFiniteComparisons.comparison2970
#print axioms sourceMap2970_checked
#print axioms fusedMap2970_checked
#print axioms certified2970
def sourceMap2970swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2970swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2970swap_checked : acceptsGraphIso
    (source (graph core2970) (root 10) 4 0) DegreeTwoThreeSpectrum6965.graph sourceMap2970swap=true := by decide +kernel
theorem fusedMap2970swap_checked : acceptsGraphIso
    (fused (graph core2970) (root 10) 4 0) DegreeTwoThreeSpectrum6966.graph fusedMap2970swap=true := by decide +kernel
theorem certified2970swap : Certified (graph core2970) (root 10) 4 0 :=
  of_native_maps core2970 DegreeTwoThreeSpectrum6965.graph DegreeTwoThreeSpectrum6966.graph
    sourceMap2970swap fusedMap2970swap sourceMap2970swap_checked fusedMap2970swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2970
#print axioms sourceMap2970swap_checked
#print axioms fusedMap2970swap_checked
#print axioms certified2970swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
