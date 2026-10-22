/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3340 : Family 9 := level9.get ⟨347,by decide⟩
def sourceMap3340 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3340 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3340_checked : acceptsGraphIso
    (source (graph core3340) (root 9) 0 5) DegreeTwoThreeSpectrum6142.graph sourceMap3340=true := by decide +kernel
theorem fusedMap3340_checked : acceptsGraphIso
    (fused (graph core3340) (root 9) 0 5) DegreeTwoThreeSpectrum5189.graph fusedMap3340=true := by decide +kernel
theorem certified3340 : Certified (graph core3340) (root 9) 0 5 :=
  of_native_maps core3340 DegreeTwoThreeSpectrum6142.graph DegreeTwoThreeSpectrum5189.graph
    sourceMap3340 fusedMap3340 sourceMap3340_checked fusedMap3340_checked
    DegreeTwoThreeFiniteComparisons.comparison3340
#print axioms sourceMap3340_checked
#print axioms fusedMap3340_checked
#print axioms certified3340
def sourceMap3340swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3340swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3340swap_checked : acceptsGraphIso
    (source (graph core3340) (root 9) 5 0) DegreeTwoThreeSpectrum6142.graph sourceMap3340swap=true := by decide +kernel
theorem fusedMap3340swap_checked : acceptsGraphIso
    (fused (graph core3340) (root 9) 5 0) DegreeTwoThreeSpectrum5189.graph fusedMap3340swap=true := by decide +kernel
theorem certified3340swap : Certified (graph core3340) (root 9) 5 0 :=
  of_native_maps core3340 DegreeTwoThreeSpectrum6142.graph DegreeTwoThreeSpectrum5189.graph
    sourceMap3340swap fusedMap3340swap sourceMap3340swap_checked fusedMap3340swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3340
#print axioms sourceMap3340swap_checked
#print axioms fusedMap3340swap_checked
#print axioms certified3340swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
