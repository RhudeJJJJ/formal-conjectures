/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2512 : Family 10 := level10.get ⟨256,by decide⟩
def sourceMap2512 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2512 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2512_checked : acceptsGraphIso
    (source (graph core2512) (root 10) 0 4) DegreeTwoThreeSpectrum5356.graph sourceMap2512=true := by decide +kernel
theorem fusedMap2512_checked : acceptsGraphIso
    (fused (graph core2512) (root 10) 0 4) DegreeTwoThreeSpectrum5357.graph fusedMap2512=true := by decide +kernel
theorem certified2512 : Certified (graph core2512) (root 10) 0 4 :=
  of_native_maps core2512 DegreeTwoThreeSpectrum5356.graph DegreeTwoThreeSpectrum5357.graph
    sourceMap2512 fusedMap2512 sourceMap2512_checked fusedMap2512_checked
    DegreeTwoThreeFiniteComparisons.comparison2512
#print axioms sourceMap2512_checked
#print axioms fusedMap2512_checked
#print axioms certified2512
def sourceMap2512swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2512swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2512swap_checked : acceptsGraphIso
    (source (graph core2512) (root 10) 4 0) DegreeTwoThreeSpectrum5356.graph sourceMap2512swap=true := by decide +kernel
theorem fusedMap2512swap_checked : acceptsGraphIso
    (fused (graph core2512) (root 10) 4 0) DegreeTwoThreeSpectrum5357.graph fusedMap2512swap=true := by decide +kernel
theorem certified2512swap : Certified (graph core2512) (root 10) 4 0 :=
  of_native_maps core2512 DegreeTwoThreeSpectrum5356.graph DegreeTwoThreeSpectrum5357.graph
    sourceMap2512swap fusedMap2512swap sourceMap2512swap_checked fusedMap2512swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2512
#print axioms sourceMap2512swap_checked
#print axioms fusedMap2512swap_checked
#print axioms certified2512swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
