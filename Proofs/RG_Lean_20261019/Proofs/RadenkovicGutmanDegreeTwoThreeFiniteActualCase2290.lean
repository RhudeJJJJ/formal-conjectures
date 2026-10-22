/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2290 : Family 9 := level9.get ⟨269,by decide⟩
def sourceMap2290 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2290 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2290_checked : acceptsGraphIso
    (source (graph core2290) (root 9) 0 4) DegreeTwoThreeSpectrum4598.graph sourceMap2290=true := by decide +kernel
theorem fusedMap2290_checked : acceptsGraphIso
    (fused (graph core2290) (root 9) 0 4) DegreeTwoThreeSpectrum4082.graph fusedMap2290=true := by decide +kernel
theorem certified2290 : Certified (graph core2290) (root 9) 0 4 :=
  of_native_maps core2290 DegreeTwoThreeSpectrum4598.graph DegreeTwoThreeSpectrum4082.graph
    sourceMap2290 fusedMap2290 sourceMap2290_checked fusedMap2290_checked
    DegreeTwoThreeFiniteComparisons.comparison2290
#print axioms sourceMap2290_checked
#print axioms fusedMap2290_checked
#print axioms certified2290
def sourceMap2290swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2290swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2290swap_checked : acceptsGraphIso
    (source (graph core2290) (root 9) 4 0) DegreeTwoThreeSpectrum4598.graph sourceMap2290swap=true := by decide +kernel
theorem fusedMap2290swap_checked : acceptsGraphIso
    (fused (graph core2290) (root 9) 4 0) DegreeTwoThreeSpectrum4082.graph fusedMap2290swap=true := by decide +kernel
theorem certified2290swap : Certified (graph core2290) (root 9) 4 0 :=
  of_native_maps core2290 DegreeTwoThreeSpectrum4598.graph DegreeTwoThreeSpectrum4082.graph
    sourceMap2290swap fusedMap2290swap sourceMap2290swap_checked fusedMap2290swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2290
#print axioms sourceMap2290swap_checked
#print axioms fusedMap2290swap_checked
#print axioms certified2290swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
