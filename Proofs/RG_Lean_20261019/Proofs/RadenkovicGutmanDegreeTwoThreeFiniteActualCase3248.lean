/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3248 : Family 9 := level9.get ⟨66,by decide⟩
def sourceMap3248 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3248 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3248_checked : acceptsGraphIso
    (source (graph core3248) (root 9) 0 5) DegreeTwoThreeSpectrum5412.graph sourceMap3248=true := by decide +kernel
theorem fusedMap3248_checked : acceptsGraphIso
    (fused (graph core3248) (root 9) 0 5) DegreeTwoThreeSpectrum4996.graph fusedMap3248=true := by decide +kernel
theorem certified3248 : Certified (graph core3248) (root 9) 0 5 :=
  of_native_maps core3248 DegreeTwoThreeSpectrum5412.graph DegreeTwoThreeSpectrum4996.graph
    sourceMap3248 fusedMap3248 sourceMap3248_checked fusedMap3248_checked
    DegreeTwoThreeFiniteComparisons.comparison3248
#print axioms sourceMap3248_checked
#print axioms fusedMap3248_checked
#print axioms certified3248
def sourceMap3248swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3248swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3248swap_checked : acceptsGraphIso
    (source (graph core3248) (root 9) 5 0) DegreeTwoThreeSpectrum5412.graph sourceMap3248swap=true := by decide +kernel
theorem fusedMap3248swap_checked : acceptsGraphIso
    (fused (graph core3248) (root 9) 5 0) DegreeTwoThreeSpectrum4996.graph fusedMap3248swap=true := by decide +kernel
theorem certified3248swap : Certified (graph core3248) (root 9) 5 0 :=
  of_native_maps core3248 DegreeTwoThreeSpectrum5412.graph DegreeTwoThreeSpectrum4996.graph
    sourceMap3248swap fusedMap3248swap sourceMap3248swap_checked fusedMap3248swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3248
#print axioms sourceMap3248swap_checked
#print axioms fusedMap3248swap_checked
#print axioms certified3248swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
