/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3164 : Family 8 := level8.get ⟨91,by decide⟩
def sourceMap3164 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3164 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3164_checked : acceptsGraphIso
    (source (graph core3164) (root 8) 0 5) DegreeTwoThreeSpectrum4153.graph sourceMap3164=true := by decide +kernel
theorem fusedMap3164_checked : acceptsGraphIso
    (fused (graph core3164) (root 8) 0 5) DegreeTwoThreeSpectrum4154.graph fusedMap3164=true := by decide +kernel
theorem certified3164 : Certified (graph core3164) (root 8) 0 5 :=
  of_native_maps core3164 DegreeTwoThreeSpectrum4153.graph DegreeTwoThreeSpectrum4154.graph
    sourceMap3164 fusedMap3164 sourceMap3164_checked fusedMap3164_checked
    DegreeTwoThreeFiniteComparisons.comparison3164
#print axioms sourceMap3164_checked
#print axioms fusedMap3164_checked
#print axioms certified3164
def sourceMap3164swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3164swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3164swap_checked : acceptsGraphIso
    (source (graph core3164) (root 8) 5 0) DegreeTwoThreeSpectrum4153.graph sourceMap3164swap=true := by decide +kernel
theorem fusedMap3164swap_checked : acceptsGraphIso
    (fused (graph core3164) (root 8) 5 0) DegreeTwoThreeSpectrum4154.graph fusedMap3164swap=true := by decide +kernel
theorem certified3164swap : Certified (graph core3164) (root 8) 5 0 :=
  of_native_maps core3164 DegreeTwoThreeSpectrum4153.graph DegreeTwoThreeSpectrum4154.graph
    sourceMap3164swap fusedMap3164swap sourceMap3164swap_checked fusedMap3164swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3164
#print axioms sourceMap3164swap_checked
#print axioms fusedMap3164swap_checked
#print axioms certified3164swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
