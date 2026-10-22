/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3159 : Family 8 := level8.get ⟨80,by decide⟩
def sourceMap3159 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3159 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3159_checked : acceptsGraphIso
    (source (graph core3159) (root 8) 0 5) DegreeTwoThreeSpectrum4100.graph sourceMap3159=true := by decide +kernel
theorem fusedMap3159_checked : acceptsGraphIso
    (fused (graph core3159) (root 8) 0 5) DegreeTwoThreeSpectrum4101.graph fusedMap3159=true := by decide +kernel
theorem certified3159 : Certified (graph core3159) (root 8) 0 5 :=
  of_native_maps core3159 DegreeTwoThreeSpectrum4100.graph DegreeTwoThreeSpectrum4101.graph
    sourceMap3159 fusedMap3159 sourceMap3159_checked fusedMap3159_checked
    DegreeTwoThreeFiniteComparisons.comparison3159
#print axioms sourceMap3159_checked
#print axioms fusedMap3159_checked
#print axioms certified3159
def sourceMap3159swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3159swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3159swap_checked : acceptsGraphIso
    (source (graph core3159) (root 8) 5 0) DegreeTwoThreeSpectrum4100.graph sourceMap3159swap=true := by decide +kernel
theorem fusedMap3159swap_checked : acceptsGraphIso
    (fused (graph core3159) (root 8) 5 0) DegreeTwoThreeSpectrum4101.graph fusedMap3159swap=true := by decide +kernel
theorem certified3159swap : Certified (graph core3159) (root 8) 5 0 :=
  of_native_maps core3159 DegreeTwoThreeSpectrum4100.graph DegreeTwoThreeSpectrum4101.graph
    sourceMap3159swap fusedMap3159swap sourceMap3159swap_checked fusedMap3159swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3159
#print axioms sourceMap3159swap_checked
#print axioms fusedMap3159swap_checked
#print axioms certified3159swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
