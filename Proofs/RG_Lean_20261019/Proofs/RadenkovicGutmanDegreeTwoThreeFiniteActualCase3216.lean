/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3216 : Family 8 := level8.get ⟨219,by decide⟩
def sourceMap3216 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3216 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3216_checked : acceptsGraphIso
    (source (graph core3216) (root 8) 0 5) DegreeTwoThreeSpectrum4308.graph sourceMap3216=true := by decide +kernel
theorem fusedMap3216_checked : acceptsGraphIso
    (fused (graph core3216) (root 8) 0 5) DegreeTwoThreeSpectrum4309.graph fusedMap3216=true := by decide +kernel
theorem certified3216 : Certified (graph core3216) (root 8) 0 5 :=
  of_native_maps core3216 DegreeTwoThreeSpectrum4308.graph DegreeTwoThreeSpectrum4309.graph
    sourceMap3216 fusedMap3216 sourceMap3216_checked fusedMap3216_checked
    DegreeTwoThreeFiniteComparisons.comparison3216
#print axioms sourceMap3216_checked
#print axioms fusedMap3216_checked
#print axioms certified3216
def sourceMap3216swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3216swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3216swap_checked : acceptsGraphIso
    (source (graph core3216) (root 8) 5 0) DegreeTwoThreeSpectrum4308.graph sourceMap3216swap=true := by decide +kernel
theorem fusedMap3216swap_checked : acceptsGraphIso
    (fused (graph core3216) (root 8) 5 0) DegreeTwoThreeSpectrum4309.graph fusedMap3216swap=true := by decide +kernel
theorem certified3216swap : Certified (graph core3216) (root 8) 5 0 :=
  of_native_maps core3216 DegreeTwoThreeSpectrum4308.graph DegreeTwoThreeSpectrum4309.graph
    sourceMap3216swap fusedMap3216swap sourceMap3216swap_checked fusedMap3216swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3216
#print axioms sourceMap3216swap_checked
#print axioms fusedMap3216swap_checked
#print axioms certified3216swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
