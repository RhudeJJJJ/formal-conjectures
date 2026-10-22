/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2496 : Family 10 := level10.get ⟨186,by decide⟩
def sourceMap2496 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,7,8,9,10,2,3,4,5,6] (sourceLabel 10 0 4 v)
def fusedMap2496 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,7,8,9,1,2,3,4,5,6] (fusedLabel 10 0 4 v)
theorem sourceMap2496_checked : acceptsGraphIso
    (source (graph core2496) (root 10) 0 4) DegreeTwoThreeSpectrum5933.graph sourceMap2496=true := by decide +kernel
theorem fusedMap2496_checked : acceptsGraphIso
    (fused (graph core2496) (root 10) 0 4) DegreeTwoThreeSpectrum5125.graph fusedMap2496=true := by decide +kernel
theorem certified2496 : Certified (graph core2496) (root 10) 0 4 :=
  of_native_maps core2496 DegreeTwoThreeSpectrum5933.graph DegreeTwoThreeSpectrum5125.graph
    sourceMap2496 fusedMap2496 sourceMap2496_checked fusedMap2496_checked
    DegreeTwoThreeFiniteComparisons.comparison2496
#print axioms sourceMap2496_checked
#print axioms fusedMap2496_checked
#print axioms certified2496
def sourceMap2496swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,7,8,9,2,3,4,5,6,10] (sourceLabel 10 4 0 v)
def fusedMap2496swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,7,8,9,1,2,3,4,5,6] (fusedLabel 10 4 0 v)
theorem sourceMap2496swap_checked : acceptsGraphIso
    (source (graph core2496) (root 10) 4 0) DegreeTwoThreeSpectrum5933.graph sourceMap2496swap=true := by decide +kernel
theorem fusedMap2496swap_checked : acceptsGraphIso
    (fused (graph core2496) (root 10) 4 0) DegreeTwoThreeSpectrum5125.graph fusedMap2496swap=true := by decide +kernel
theorem certified2496swap : Certified (graph core2496) (root 10) 4 0 :=
  of_native_maps core2496 DegreeTwoThreeSpectrum5933.graph DegreeTwoThreeSpectrum5125.graph
    sourceMap2496swap fusedMap2496swap sourceMap2496swap_checked fusedMap2496swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2496
#print axioms sourceMap2496swap_checked
#print axioms fusedMap2496swap_checked
#print axioms certified2496swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
