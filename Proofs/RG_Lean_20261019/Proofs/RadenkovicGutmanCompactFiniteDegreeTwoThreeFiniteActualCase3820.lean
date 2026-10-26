/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3820 : Family 7 := level7.get ⟨88,by decide⟩
def sourceMap3820 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3820 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3820_checked : acceptsGraphIso
    (source (graph core3820) (root 7) 1 4) DegreeTwoThreeSpectrum3498.graph sourceMap3820=true := by decide +kernel
theorem fusedMap3820_checked : acceptsGraphIso
    (fused (graph core3820) (root 7) 1 4) DegreeTwoThreeSpectrum2706.graph fusedMap3820=true := by decide +kernel
theorem certified3820 : Certified (graph core3820) (root 7) 1 4 :=
  of_native_maps core3820 DegreeTwoThreeSpectrum3498.graph DegreeTwoThreeSpectrum2706.graph
    sourceMap3820 fusedMap3820 sourceMap3820_checked fusedMap3820_checked
    DegreeTwoThreeFiniteComparisons.comparison3820
#print axioms sourceMap3820_checked
#print axioms fusedMap3820_checked
#print axioms certified3820
def sourceMap3820swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,9,10] (sourceLabel 7 4 1 v)
def fusedMap3820swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3820swap_checked : acceptsGraphIso
    (source (graph core3820) (root 7) 4 1) DegreeTwoThreeSpectrum3498.graph sourceMap3820swap=true := by decide +kernel
theorem fusedMap3820swap_checked : acceptsGraphIso
    (fused (graph core3820) (root 7) 4 1) DegreeTwoThreeSpectrum2706.graph fusedMap3820swap=true := by decide +kernel
theorem certified3820swap : Certified (graph core3820) (root 7) 4 1 :=
  of_native_maps core3820 DegreeTwoThreeSpectrum3498.graph DegreeTwoThreeSpectrum2706.graph
    sourceMap3820swap fusedMap3820swap sourceMap3820swap_checked fusedMap3820swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3820
#print axioms sourceMap3820swap_checked
#print axioms fusedMap3820swap_checked
#print axioms certified3820swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
