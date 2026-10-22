/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3214 : Family 8 := level8.get ⟨216,by decide⟩
def sourceMap3214 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3214 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3214_checked : acceptsGraphIso
    (source (graph core3214) (root 8) 0 5) DegreeTwoThreeSpectrum4294.graph sourceMap3214=true := by decide +kernel
theorem fusedMap3214_checked : acceptsGraphIso
    (fused (graph core3214) (root 8) 0 5) DegreeTwoThreeSpectrum4295.graph fusedMap3214=true := by decide +kernel
theorem certified3214 : Certified (graph core3214) (root 8) 0 5 :=
  of_native_maps core3214 DegreeTwoThreeSpectrum4294.graph DegreeTwoThreeSpectrum4295.graph
    sourceMap3214 fusedMap3214 sourceMap3214_checked fusedMap3214_checked
    DegreeTwoThreeFiniteComparisons.comparison3214
#print axioms sourceMap3214_checked
#print axioms fusedMap3214_checked
#print axioms certified3214
def sourceMap3214swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3214swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3214swap_checked : acceptsGraphIso
    (source (graph core3214) (root 8) 5 0) DegreeTwoThreeSpectrum4294.graph sourceMap3214swap=true := by decide +kernel
theorem fusedMap3214swap_checked : acceptsGraphIso
    (fused (graph core3214) (root 8) 5 0) DegreeTwoThreeSpectrum4295.graph fusedMap3214swap=true := by decide +kernel
theorem certified3214swap : Certified (graph core3214) (root 8) 5 0 :=
  of_native_maps core3214 DegreeTwoThreeSpectrum4294.graph DegreeTwoThreeSpectrum4295.graph
    sourceMap3214swap fusedMap3214swap sourceMap3214swap_checked fusedMap3214swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3214
#print axioms sourceMap3214swap_checked
#print axioms fusedMap3214swap_checked
#print axioms certified3214swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
