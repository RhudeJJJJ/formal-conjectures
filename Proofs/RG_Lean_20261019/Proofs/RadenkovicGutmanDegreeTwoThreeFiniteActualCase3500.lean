/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3500 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap3500 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3500 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3500_checked : acceptsGraphIso
    (source (graph core3500) (root 6) 0 6) DegreeTwoThreeSpectrum2456.graph sourceMap3500=true := by decide +kernel
theorem fusedMap3500_checked : acceptsGraphIso
    (fused (graph core3500) (root 6) 0 6) DegreeTwoThreeSpectrum2459.graph fusedMap3500=true := by decide +kernel
theorem certified3500 : Certified (graph core3500) (root 6) 0 6 :=
  of_native_maps core3500 DegreeTwoThreeSpectrum2456.graph DegreeTwoThreeSpectrum2459.graph
    sourceMap3500 fusedMap3500 sourceMap3500_checked fusedMap3500_checked
    DegreeTwoThreeFiniteComparisons.comparison3500
#print axioms sourceMap3500_checked
#print axioms fusedMap3500_checked
#print axioms certified3500
def sourceMap3500swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,9] (sourceLabel 6 6 0 v)
def fusedMap3500swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3500swap_checked : acceptsGraphIso
    (source (graph core3500) (root 6) 6 0) DegreeTwoThreeSpectrum2456.graph sourceMap3500swap=true := by decide +kernel
theorem fusedMap3500swap_checked : acceptsGraphIso
    (fused (graph core3500) (root 6) 6 0) DegreeTwoThreeSpectrum2459.graph fusedMap3500swap=true := by decide +kernel
theorem certified3500swap : Certified (graph core3500) (root 6) 6 0 :=
  of_native_maps core3500 DegreeTwoThreeSpectrum2456.graph DegreeTwoThreeSpectrum2459.graph
    sourceMap3500swap fusedMap3500swap sourceMap3500swap_checked fusedMap3500swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3500
#print axioms sourceMap3500swap_checked
#print axioms fusedMap3500swap_checked
#print axioms certified3500swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
