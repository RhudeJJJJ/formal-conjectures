/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3330 : Family 9 := level9.get ⟨312,by decide⟩
def sourceMap3330 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3330 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3330_checked : acceptsGraphIso
    (source (graph core3330) (root 9) 0 5) DegreeTwoThreeSpectrum5929.graph sourceMap3330=true := by decide +kernel
theorem fusedMap3330_checked : acceptsGraphIso
    (fused (graph core3330) (root 9) 0 5) DegreeTwoThreeSpectrum5930.graph fusedMap3330=true := by decide +kernel
theorem certified3330 : Certified (graph core3330) (root 9) 0 5 :=
  of_native_maps core3330 DegreeTwoThreeSpectrum5929.graph DegreeTwoThreeSpectrum5930.graph
    sourceMap3330 fusedMap3330 sourceMap3330_checked fusedMap3330_checked
    DegreeTwoThreeFiniteComparisons.comparison3330
#print axioms sourceMap3330_checked
#print axioms fusedMap3330_checked
#print axioms certified3330
def sourceMap3330swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3330swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3330swap_checked : acceptsGraphIso
    (source (graph core3330) (root 9) 5 0) DegreeTwoThreeSpectrum5929.graph sourceMap3330swap=true := by decide +kernel
theorem fusedMap3330swap_checked : acceptsGraphIso
    (fused (graph core3330) (root 9) 5 0) DegreeTwoThreeSpectrum5930.graph fusedMap3330swap=true := by decide +kernel
theorem certified3330swap : Certified (graph core3330) (root 9) 5 0 :=
  of_native_maps core3330 DegreeTwoThreeSpectrum5929.graph DegreeTwoThreeSpectrum5930.graph
    sourceMap3330swap fusedMap3330swap sourceMap3330swap_checked fusedMap3330swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3330
#print axioms sourceMap3330swap_checked
#print axioms fusedMap3330swap_checked
#print axioms certified3330swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
