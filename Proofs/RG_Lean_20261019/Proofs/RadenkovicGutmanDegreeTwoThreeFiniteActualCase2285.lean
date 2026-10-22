/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2285 : Family 9 := level9.get ⟨253,by decide⟩
def sourceMap2285 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2285 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2285_checked : acceptsGraphIso
    (source (graph core2285) (root 9) 0 4) DegreeTwoThreeSpectrum4561.graph sourceMap2285=true := by decide +kernel
theorem fusedMap2285_checked : acceptsGraphIso
    (fused (graph core2285) (root 9) 0 4) DegreeTwoThreeSpectrum4061.graph fusedMap2285=true := by decide +kernel
theorem certified2285 : Certified (graph core2285) (root 9) 0 4 :=
  of_native_maps core2285 DegreeTwoThreeSpectrum4561.graph DegreeTwoThreeSpectrum4061.graph
    sourceMap2285 fusedMap2285 sourceMap2285_checked fusedMap2285_checked
    DegreeTwoThreeFiniteComparisons.comparison2285
#print axioms sourceMap2285_checked
#print axioms fusedMap2285_checked
#print axioms certified2285
def sourceMap2285swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2285swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2285swap_checked : acceptsGraphIso
    (source (graph core2285) (root 9) 4 0) DegreeTwoThreeSpectrum4561.graph sourceMap2285swap=true := by decide +kernel
theorem fusedMap2285swap_checked : acceptsGraphIso
    (fused (graph core2285) (root 9) 4 0) DegreeTwoThreeSpectrum4061.graph fusedMap2285swap=true := by decide +kernel
theorem certified2285swap : Certified (graph core2285) (root 9) 4 0 :=
  of_native_maps core2285 DegreeTwoThreeSpectrum4561.graph DegreeTwoThreeSpectrum4061.graph
    sourceMap2285swap fusedMap2285swap sourceMap2285swap_checked fusedMap2285swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2285
#print axioms sourceMap2285swap_checked
#print axioms fusedMap2285swap_checked
#print axioms certified2285swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
