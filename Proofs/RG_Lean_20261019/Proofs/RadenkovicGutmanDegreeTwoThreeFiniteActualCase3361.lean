/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3361 : Family 9 := level9.get ⟨400,by decide⟩
def sourceMap3361 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3361 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3361_checked : acceptsGraphIso
    (source (graph core3361) (root 9) 0 5) DegreeTwoThreeSpectrum6394.graph sourceMap3361=true := by decide +kernel
theorem fusedMap3361_checked : acceptsGraphIso
    (fused (graph core3361) (root 9) 0 5) DegreeTwoThreeSpectrum5330.graph fusedMap3361=true := by decide +kernel
theorem certified3361 : Certified (graph core3361) (root 9) 0 5 :=
  of_native_maps core3361 DegreeTwoThreeSpectrum6394.graph DegreeTwoThreeSpectrum5330.graph
    sourceMap3361 fusedMap3361 sourceMap3361_checked fusedMap3361_checked
    DegreeTwoThreeFiniteComparisons.comparison3361
#print axioms sourceMap3361_checked
#print axioms fusedMap3361_checked
#print axioms certified3361
def sourceMap3361swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3361swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3361swap_checked : acceptsGraphIso
    (source (graph core3361) (root 9) 5 0) DegreeTwoThreeSpectrum6394.graph sourceMap3361swap=true := by decide +kernel
theorem fusedMap3361swap_checked : acceptsGraphIso
    (fused (graph core3361) (root 9) 5 0) DegreeTwoThreeSpectrum5330.graph fusedMap3361swap=true := by decide +kernel
theorem certified3361swap : Certified (graph core3361) (root 9) 5 0 :=
  of_native_maps core3361 DegreeTwoThreeSpectrum6394.graph DegreeTwoThreeSpectrum5330.graph
    sourceMap3361swap fusedMap3361swap sourceMap3361swap_checked fusedMap3361swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3361
#print axioms sourceMap3361swap_checked
#print axioms fusedMap3361swap_checked
#print axioms certified3361swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
