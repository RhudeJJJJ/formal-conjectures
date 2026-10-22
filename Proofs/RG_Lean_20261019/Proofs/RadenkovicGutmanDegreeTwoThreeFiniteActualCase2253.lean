/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2253 : Family 9 := level9.get ⟨154,by decide⟩
def sourceMap2253 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2253 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2253_checked : acceptsGraphIso
    (source (graph core2253) (root 9) 0 4) DegreeTwoThreeSpectrum4258.graph sourceMap2253=true := by decide +kernel
theorem fusedMap2253_checked : acceptsGraphIso
    (fused (graph core2253) (root 9) 0 4) DegreeTwoThreeSpectrum3912.graph fusedMap2253=true := by decide +kernel
theorem certified2253 : Certified (graph core2253) (root 9) 0 4 :=
  of_native_maps core2253 DegreeTwoThreeSpectrum4258.graph DegreeTwoThreeSpectrum3912.graph
    sourceMap2253 fusedMap2253 sourceMap2253_checked fusedMap2253_checked
    DegreeTwoThreeFiniteComparisons.comparison2253
#print axioms sourceMap2253_checked
#print axioms fusedMap2253_checked
#print axioms certified2253
def sourceMap2253swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2253swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2253swap_checked : acceptsGraphIso
    (source (graph core2253) (root 9) 4 0) DegreeTwoThreeSpectrum4258.graph sourceMap2253swap=true := by decide +kernel
theorem fusedMap2253swap_checked : acceptsGraphIso
    (fused (graph core2253) (root 9) 4 0) DegreeTwoThreeSpectrum3912.graph fusedMap2253swap=true := by decide +kernel
theorem certified2253swap : Certified (graph core2253) (root 9) 4 0 :=
  of_native_maps core2253 DegreeTwoThreeSpectrum4258.graph DegreeTwoThreeSpectrum3912.graph
    sourceMap2253swap fusedMap2253swap sourceMap2253swap_checked fusedMap2253swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2253
#print axioms sourceMap2253swap_checked
#print axioms fusedMap2253swap_checked
#print axioms certified2253swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
