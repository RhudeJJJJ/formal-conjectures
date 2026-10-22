/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2875 : Family 10 := level10.get ⟨1262,by decide⟩
def sourceMap2875 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2875 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2875_checked : acceptsGraphIso
    (source (graph core2875) (root 10) 0 4) DegreeTwoThreeSpectrum6512.graph sourceMap2875=true := by decide +kernel
theorem fusedMap2875_checked : acceptsGraphIso
    (fused (graph core2875) (root 10) 0 4) DegreeTwoThreeSpectrum6513.graph fusedMap2875=true := by decide +kernel
theorem certified2875 : Certified (graph core2875) (root 10) 0 4 :=
  of_native_maps core2875 DegreeTwoThreeSpectrum6512.graph DegreeTwoThreeSpectrum6513.graph
    sourceMap2875 fusedMap2875 sourceMap2875_checked fusedMap2875_checked
    DegreeTwoThreeFiniteComparisons.comparison2875
#print axioms sourceMap2875_checked
#print axioms fusedMap2875_checked
#print axioms certified2875
def sourceMap2875swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2875swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2875swap_checked : acceptsGraphIso
    (source (graph core2875) (root 10) 4 0) DegreeTwoThreeSpectrum6512.graph sourceMap2875swap=true := by decide +kernel
theorem fusedMap2875swap_checked : acceptsGraphIso
    (fused (graph core2875) (root 10) 4 0) DegreeTwoThreeSpectrum6513.graph fusedMap2875swap=true := by decide +kernel
theorem certified2875swap : Certified (graph core2875) (root 10) 4 0 :=
  of_native_maps core2875 DegreeTwoThreeSpectrum6512.graph DegreeTwoThreeSpectrum6513.graph
    sourceMap2875swap fusedMap2875swap sourceMap2875swap_checked fusedMap2875swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2875
#print axioms sourceMap2875swap_checked
#print axioms fusedMap2875swap_checked
#print axioms certified2875swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
