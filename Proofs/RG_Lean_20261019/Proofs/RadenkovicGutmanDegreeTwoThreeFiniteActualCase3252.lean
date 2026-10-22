/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3252 : Family 9 := level9.get ⟨83,by decide⟩
def sourceMap3252 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3252 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3252_checked : acceptsGraphIso
    (source (graph core3252) (root 9) 0 5) DegreeTwoThreeSpectrum5595.graph sourceMap3252=true := by decide +kernel
theorem fusedMap3252_checked : acceptsGraphIso
    (fused (graph core3252) (root 9) 0 5) DegreeTwoThreeSpectrum5025.graph fusedMap3252=true := by decide +kernel
theorem certified3252 : Certified (graph core3252) (root 9) 0 5 :=
  of_native_maps core3252 DegreeTwoThreeSpectrum5595.graph DegreeTwoThreeSpectrum5025.graph
    sourceMap3252 fusedMap3252 sourceMap3252_checked fusedMap3252_checked
    DegreeTwoThreeFiniteComparisons.comparison3252
#print axioms sourceMap3252_checked
#print axioms fusedMap3252_checked
#print axioms certified3252
def sourceMap3252swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3252swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3252swap_checked : acceptsGraphIso
    (source (graph core3252) (root 9) 5 0) DegreeTwoThreeSpectrum5595.graph sourceMap3252swap=true := by decide +kernel
theorem fusedMap3252swap_checked : acceptsGraphIso
    (fused (graph core3252) (root 9) 5 0) DegreeTwoThreeSpectrum5025.graph fusedMap3252swap=true := by decide +kernel
theorem certified3252swap : Certified (graph core3252) (root 9) 5 0 :=
  of_native_maps core3252 DegreeTwoThreeSpectrum5595.graph DegreeTwoThreeSpectrum5025.graph
    sourceMap3252swap fusedMap3252swap sourceMap3252swap_checked fusedMap3252swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3252
#print axioms sourceMap3252swap_checked
#print axioms fusedMap3252swap_checked
#print axioms certified3252swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
