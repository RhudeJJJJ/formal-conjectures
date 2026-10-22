/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3439 : Family 9 := level9.get ⟨588,by decide⟩
def sourceMap3439 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3439 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3439_checked : acceptsGraphIso
    (source (graph core3439) (root 9) 0 5) DegreeTwoThreeSpectrum6181.graph sourceMap3439=true := by decide +kernel
theorem fusedMap3439_checked : acceptsGraphIso
    (fused (graph core3439) (root 9) 0 5) DegreeTwoThreeSpectrum6182.graph fusedMap3439=true := by decide +kernel
theorem certified3439 : Certified (graph core3439) (root 9) 0 5 :=
  of_native_maps core3439 DegreeTwoThreeSpectrum6181.graph DegreeTwoThreeSpectrum6182.graph
    sourceMap3439 fusedMap3439 sourceMap3439_checked fusedMap3439_checked
    DegreeTwoThreeFiniteComparisons.comparison3439
#print axioms sourceMap3439_checked
#print axioms fusedMap3439_checked
#print axioms certified3439
def sourceMap3439swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3439swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3439swap_checked : acceptsGraphIso
    (source (graph core3439) (root 9) 5 0) DegreeTwoThreeSpectrum6181.graph sourceMap3439swap=true := by decide +kernel
theorem fusedMap3439swap_checked : acceptsGraphIso
    (fused (graph core3439) (root 9) 5 0) DegreeTwoThreeSpectrum6182.graph fusedMap3439swap=true := by decide +kernel
theorem certified3439swap : Certified (graph core3439) (root 9) 5 0 :=
  of_native_maps core3439 DegreeTwoThreeSpectrum6181.graph DegreeTwoThreeSpectrum6182.graph
    sourceMap3439swap fusedMap3439swap sourceMap3439swap_checked fusedMap3439swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3439
#print axioms sourceMap3439swap_checked
#print axioms fusedMap3439swap_checked
#print axioms certified3439swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
