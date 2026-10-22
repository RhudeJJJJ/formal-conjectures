/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3186 : Family 8 := level8.get ⟨154,by decide⟩
def sourceMap3186 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3186 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3186_checked : acceptsGraphIso
    (source (graph core3186) (root 8) 0 5) DegreeTwoThreeSpectrum4505.graph sourceMap3186=true := by decide +kernel
theorem fusedMap3186_checked : acceptsGraphIso
    (fused (graph core3186) (root 8) 0 5) DegreeTwoThreeSpectrum4024.graph fusedMap3186=true := by decide +kernel
theorem certified3186 : Certified (graph core3186) (root 8) 0 5 :=
  of_native_maps core3186 DegreeTwoThreeSpectrum4505.graph DegreeTwoThreeSpectrum4024.graph
    sourceMap3186 fusedMap3186 sourceMap3186_checked fusedMap3186_checked
    DegreeTwoThreeFiniteComparisons.comparison3186
#print axioms sourceMap3186_checked
#print axioms fusedMap3186_checked
#print axioms certified3186
def sourceMap3186swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3186swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3186swap_checked : acceptsGraphIso
    (source (graph core3186) (root 8) 5 0) DegreeTwoThreeSpectrum4505.graph sourceMap3186swap=true := by decide +kernel
theorem fusedMap3186swap_checked : acceptsGraphIso
    (fused (graph core3186) (root 8) 5 0) DegreeTwoThreeSpectrum4024.graph fusedMap3186swap=true := by decide +kernel
theorem certified3186swap : Certified (graph core3186) (root 8) 5 0 :=
  of_native_maps core3186 DegreeTwoThreeSpectrum4505.graph DegreeTwoThreeSpectrum4024.graph
    sourceMap3186swap fusedMap3186swap sourceMap3186swap_checked fusedMap3186swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3186
#print axioms sourceMap3186swap_checked
#print axioms fusedMap3186swap_checked
#print axioms certified3186swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
