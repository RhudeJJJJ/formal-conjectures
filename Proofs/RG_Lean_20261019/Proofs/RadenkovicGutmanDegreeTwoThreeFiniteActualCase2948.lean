/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2948 : Family 10 := level10.get ⟨1432,by decide⟩
def sourceMap2948 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2948 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2948_checked : acceptsGraphIso
    (source (graph core2948) (root 10) 0 4) DegreeTwoThreeSpectrum6889.graph sourceMap2948=true := by decide +kernel
theorem fusedMap2948_checked : acceptsGraphIso
    (fused (graph core2948) (root 10) 0 4) DegreeTwoThreeSpectrum6890.graph fusedMap2948=true := by decide +kernel
theorem certified2948 : Certified (graph core2948) (root 10) 0 4 :=
  of_native_maps core2948 DegreeTwoThreeSpectrum6889.graph DegreeTwoThreeSpectrum6890.graph
    sourceMap2948 fusedMap2948 sourceMap2948_checked fusedMap2948_checked
    DegreeTwoThreeFiniteComparisons.comparison2948
#print axioms sourceMap2948_checked
#print axioms fusedMap2948_checked
#print axioms certified2948
def sourceMap2948swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2948swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2948swap_checked : acceptsGraphIso
    (source (graph core2948) (root 10) 4 0) DegreeTwoThreeSpectrum6889.graph sourceMap2948swap=true := by decide +kernel
theorem fusedMap2948swap_checked : acceptsGraphIso
    (fused (graph core2948) (root 10) 4 0) DegreeTwoThreeSpectrum6890.graph fusedMap2948swap=true := by decide +kernel
theorem certified2948swap : Certified (graph core2948) (root 10) 4 0 :=
  of_native_maps core2948 DegreeTwoThreeSpectrum6889.graph DegreeTwoThreeSpectrum6890.graph
    sourceMap2948swap fusedMap2948swap sourceMap2948swap_checked fusedMap2948swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2948
#print axioms sourceMap2948swap_checked
#print axioms fusedMap2948swap_checked
#print axioms certified2948swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
