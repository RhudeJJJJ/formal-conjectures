/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3443 : Family 9 := level9.get ⟨596,by decide⟩
def sourceMap3443 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3443 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3443_checked : acceptsGraphIso
    (source (graph core3443) (root 9) 0 5) DegreeTwoThreeSpectrum6215.graph sourceMap3443=true := by decide +kernel
theorem fusedMap3443_checked : acceptsGraphIso
    (fused (graph core3443) (root 9) 0 5) DegreeTwoThreeSpectrum6216.graph fusedMap3443=true := by decide +kernel
theorem certified3443 : Certified (graph core3443) (root 9) 0 5 :=
  of_native_maps core3443 DegreeTwoThreeSpectrum6215.graph DegreeTwoThreeSpectrum6216.graph
    sourceMap3443 fusedMap3443 sourceMap3443_checked fusedMap3443_checked
    DegreeTwoThreeFiniteComparisons.comparison3443
#print axioms sourceMap3443_checked
#print axioms fusedMap3443_checked
#print axioms certified3443
def sourceMap3443swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3443swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3443swap_checked : acceptsGraphIso
    (source (graph core3443) (root 9) 5 0) DegreeTwoThreeSpectrum6215.graph sourceMap3443swap=true := by decide +kernel
theorem fusedMap3443swap_checked : acceptsGraphIso
    (fused (graph core3443) (root 9) 5 0) DegreeTwoThreeSpectrum6216.graph fusedMap3443swap=true := by decide +kernel
theorem certified3443swap : Certified (graph core3443) (root 9) 5 0 :=
  of_native_maps core3443 DegreeTwoThreeSpectrum6215.graph DegreeTwoThreeSpectrum6216.graph
    sourceMap3443swap fusedMap3443swap sourceMap3443swap_checked fusedMap3443swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3443
#print axioms sourceMap3443swap_checked
#print axioms fusedMap3443swap_checked
#print axioms certified3443swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
