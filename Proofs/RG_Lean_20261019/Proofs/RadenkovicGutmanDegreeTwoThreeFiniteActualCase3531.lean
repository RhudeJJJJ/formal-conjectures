/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3531 : Family 7 := level7.get ⟨87,by decide⟩
def sourceMap3531 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3531 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3531_checked : acceptsGraphIso
    (source (graph core3531) (root 7) 0 6) DegreeTwoThreeSpectrum4449.graph sourceMap3531=true := by decide +kernel
theorem fusedMap3531_checked : acceptsGraphIso
    (fused (graph core3531) (root 7) 0 6) DegreeTwoThreeSpectrum4001.graph fusedMap3531=true := by decide +kernel
theorem certified3531 : Certified (graph core3531) (root 7) 0 6 :=
  of_native_maps core3531 DegreeTwoThreeSpectrum4449.graph DegreeTwoThreeSpectrum4001.graph
    sourceMap3531 fusedMap3531 sourceMap3531_checked fusedMap3531_checked
    DegreeTwoThreeFiniteComparisons.comparison3531
#print axioms sourceMap3531_checked
#print axioms fusedMap3531_checked
#print axioms certified3531
def sourceMap3531swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3531swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3531swap_checked : acceptsGraphIso
    (source (graph core3531) (root 7) 6 0) DegreeTwoThreeSpectrum4449.graph sourceMap3531swap=true := by decide +kernel
theorem fusedMap3531swap_checked : acceptsGraphIso
    (fused (graph core3531) (root 7) 6 0) DegreeTwoThreeSpectrum4001.graph fusedMap3531swap=true := by decide +kernel
theorem certified3531swap : Certified (graph core3531) (root 7) 6 0 :=
  of_native_maps core3531 DegreeTwoThreeSpectrum4449.graph DegreeTwoThreeSpectrum4001.graph
    sourceMap3531swap fusedMap3531swap sourceMap3531swap_checked fusedMap3531swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3531
#print axioms sourceMap3531swap_checked
#print axioms fusedMap3531swap_checked
#print axioms certified3531swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
