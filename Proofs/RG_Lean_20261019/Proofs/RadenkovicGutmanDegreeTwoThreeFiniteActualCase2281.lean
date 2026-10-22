/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2281 : Family 9 := level9.get ⟨244,by decide⟩
def sourceMap2281 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2281 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2281_checked : acceptsGraphIso
    (source (graph core2281) (root 9) 0 4) DegreeTwoThreeSpectrum4530.graph sourceMap2281=true := by decide +kernel
theorem fusedMap2281_checked : acceptsGraphIso
    (fused (graph core2281) (root 9) 0 4) DegreeTwoThreeSpectrum4041.graph fusedMap2281=true := by decide +kernel
theorem certified2281 : Certified (graph core2281) (root 9) 0 4 :=
  of_native_maps core2281 DegreeTwoThreeSpectrum4530.graph DegreeTwoThreeSpectrum4041.graph
    sourceMap2281 fusedMap2281 sourceMap2281_checked fusedMap2281_checked
    DegreeTwoThreeFiniteComparisons.comparison2281
#print axioms sourceMap2281_checked
#print axioms fusedMap2281_checked
#print axioms certified2281
def sourceMap2281swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2281swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2281swap_checked : acceptsGraphIso
    (source (graph core2281) (root 9) 4 0) DegreeTwoThreeSpectrum4530.graph sourceMap2281swap=true := by decide +kernel
theorem fusedMap2281swap_checked : acceptsGraphIso
    (fused (graph core2281) (root 9) 4 0) DegreeTwoThreeSpectrum4041.graph fusedMap2281swap=true := by decide +kernel
theorem certified2281swap : Certified (graph core2281) (root 9) 4 0 :=
  of_native_maps core2281 DegreeTwoThreeSpectrum4530.graph DegreeTwoThreeSpectrum4041.graph
    sourceMap2281swap fusedMap2281swap sourceMap2281swap_checked fusedMap2281swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2281
#print axioms sourceMap2281swap_checked
#print axioms fusedMap2281swap_checked
#print axioms certified2281swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
