/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2866 : Family 10 := level10.get ⟨1229,by decide⟩
def sourceMap2866 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2866 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2866_checked : acceptsGraphIso
    (source (graph core2866) (root 10) 0 4) DegreeTwoThreeSpectrum6432.graph sourceMap2866=true := by decide +kernel
theorem fusedMap2866_checked : acceptsGraphIso
    (fused (graph core2866) (root 10) 0 4) DegreeTwoThreeSpectrum6433.graph fusedMap2866=true := by decide +kernel
theorem certified2866 : Certified (graph core2866) (root 10) 0 4 :=
  of_native_maps core2866 DegreeTwoThreeSpectrum6432.graph DegreeTwoThreeSpectrum6433.graph
    sourceMap2866 fusedMap2866 sourceMap2866_checked fusedMap2866_checked
    DegreeTwoThreeFiniteComparisons.comparison2866
#print axioms sourceMap2866_checked
#print axioms fusedMap2866_checked
#print axioms certified2866
def sourceMap2866swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2866swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2866swap_checked : acceptsGraphIso
    (source (graph core2866) (root 10) 4 0) DegreeTwoThreeSpectrum6432.graph sourceMap2866swap=true := by decide +kernel
theorem fusedMap2866swap_checked : acceptsGraphIso
    (fused (graph core2866) (root 10) 4 0) DegreeTwoThreeSpectrum6433.graph fusedMap2866swap=true := by decide +kernel
theorem certified2866swap : Certified (graph core2866) (root 10) 4 0 :=
  of_native_maps core2866 DegreeTwoThreeSpectrum6432.graph DegreeTwoThreeSpectrum6433.graph
    sourceMap2866swap fusedMap2866swap sourceMap2866swap_checked fusedMap2866swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2866
#print axioms sourceMap2866swap_checked
#print axioms fusedMap2866swap_checked
#print axioms certified2866swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
