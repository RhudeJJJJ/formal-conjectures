/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3222 : Family 8 := level8.get ⟨234,by decide⟩
def sourceMap3222 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3222 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3222_checked : acceptsGraphIso
    (source (graph core3222) (root 8) 0 5) DegreeTwoThreeSpectrum4405.graph sourceMap3222=true := by decide +kernel
theorem fusedMap3222_checked : acceptsGraphIso
    (fused (graph core3222) (root 8) 0 5) DegreeTwoThreeSpectrum4406.graph fusedMap3222=true := by decide +kernel
theorem certified3222 : Certified (graph core3222) (root 8) 0 5 :=
  of_native_maps core3222 DegreeTwoThreeSpectrum4405.graph DegreeTwoThreeSpectrum4406.graph
    sourceMap3222 fusedMap3222 sourceMap3222_checked fusedMap3222_checked
    DegreeTwoThreeFiniteComparisons.comparison3222
#print axioms sourceMap3222_checked
#print axioms fusedMap3222_checked
#print axioms certified3222
def sourceMap3222swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3222swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3222swap_checked : acceptsGraphIso
    (source (graph core3222) (root 8) 5 0) DegreeTwoThreeSpectrum4405.graph sourceMap3222swap=true := by decide +kernel
theorem fusedMap3222swap_checked : acceptsGraphIso
    (fused (graph core3222) (root 8) 5 0) DegreeTwoThreeSpectrum4406.graph fusedMap3222swap=true := by decide +kernel
theorem certified3222swap : Certified (graph core3222) (root 8) 5 0 :=
  of_native_maps core3222 DegreeTwoThreeSpectrum4405.graph DegreeTwoThreeSpectrum4406.graph
    sourceMap3222swap fusedMap3222swap sourceMap3222swap_checked fusedMap3222swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3222
#print axioms sourceMap3222swap_checked
#print axioms fusedMap3222swap_checked
#print axioms certified3222swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
