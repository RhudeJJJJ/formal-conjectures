/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2361 : Family 9 := level9.get ⟨452,by decide⟩
def sourceMap2361 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2361 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2361_checked : acceptsGraphIso
    (source (graph core2361) (root 9) 0 4) DegreeTwoThreeSpectrum4468.graph sourceMap2361=true := by decide +kernel
theorem fusedMap2361_checked : acceptsGraphIso
    (fused (graph core2361) (root 9) 0 4) DegreeTwoThreeSpectrum4469.graph fusedMap2361=true := by decide +kernel
theorem certified2361 : Certified (graph core2361) (root 9) 0 4 :=
  of_native_maps core2361 DegreeTwoThreeSpectrum4468.graph DegreeTwoThreeSpectrum4469.graph
    sourceMap2361 fusedMap2361 sourceMap2361_checked fusedMap2361_checked
    DegreeTwoThreeFiniteComparisons.comparison2361
#print axioms sourceMap2361_checked
#print axioms fusedMap2361_checked
#print axioms certified2361
def sourceMap2361swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2361swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2361swap_checked : acceptsGraphIso
    (source (graph core2361) (root 9) 4 0) DegreeTwoThreeSpectrum4468.graph sourceMap2361swap=true := by decide +kernel
theorem fusedMap2361swap_checked : acceptsGraphIso
    (fused (graph core2361) (root 9) 4 0) DegreeTwoThreeSpectrum4469.graph fusedMap2361swap=true := by decide +kernel
theorem certified2361swap : Certified (graph core2361) (root 9) 4 0 :=
  of_native_maps core2361 DegreeTwoThreeSpectrum4468.graph DegreeTwoThreeSpectrum4469.graph
    sourceMap2361swap fusedMap2361swap sourceMap2361swap_checked fusedMap2361swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2361
#print axioms sourceMap2361swap_checked
#print axioms fusedMap2361swap_checked
#print axioms certified2361swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
