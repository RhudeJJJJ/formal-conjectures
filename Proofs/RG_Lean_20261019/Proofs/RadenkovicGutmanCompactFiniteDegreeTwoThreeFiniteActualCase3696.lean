/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3696 : Family 7 := level7.get ⟨101,by decide⟩
def sourceMap3696 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3696 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3696_checked : acceptsGraphIso
    (source (graph core3696) (root 7) 0 7) DegreeTwoThreeSpectrum5976.graph sourceMap3696=true := by decide +kernel
theorem fusedMap3696_checked : acceptsGraphIso
    (fused (graph core3696) (root 7) 0 7) DegreeTwoThreeSpectrum5135.graph fusedMap3696=true := by decide +kernel
theorem certified3696 : Certified (graph core3696) (root 7) 0 7 :=
  of_native_maps core3696 DegreeTwoThreeSpectrum5976.graph DegreeTwoThreeSpectrum5135.graph
    sourceMap3696 fusedMap3696 sourceMap3696_checked fusedMap3696_checked
    DegreeTwoThreeFiniteComparisons.comparison3696
#print axioms sourceMap3696_checked
#print axioms fusedMap3696_checked
#print axioms certified3696
def sourceMap3696swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,12,13,14,15,16,11] (sourceLabel 7 7 0 v)
def fusedMap3696swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3696swap_checked : acceptsGraphIso
    (source (graph core3696) (root 7) 7 0) DegreeTwoThreeSpectrum5976.graph sourceMap3696swap=true := by decide +kernel
theorem fusedMap3696swap_checked : acceptsGraphIso
    (fused (graph core3696) (root 7) 7 0) DegreeTwoThreeSpectrum5135.graph fusedMap3696swap=true := by decide +kernel
theorem certified3696swap : Certified (graph core3696) (root 7) 7 0 :=
  of_native_maps core3696 DegreeTwoThreeSpectrum5976.graph DegreeTwoThreeSpectrum5135.graph
    sourceMap3696swap fusedMap3696swap sourceMap3696swap_checked fusedMap3696swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3696
#print axioms sourceMap3696swap_checked
#print axioms fusedMap3696swap_checked
#print axioms certified3696swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
