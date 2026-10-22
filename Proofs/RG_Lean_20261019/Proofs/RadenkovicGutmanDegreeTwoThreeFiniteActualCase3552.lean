/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3552 : Family 8 := level8.get ⟨60,by decide⟩
def sourceMap3552 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3552 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3552_checked : acceptsGraphIso
    (source (graph core3552) (root 8) 0 6) DegreeTwoThreeSpectrum5533.graph sourceMap3552=true := by decide +kernel
theorem fusedMap3552_checked : acceptsGraphIso
    (fused (graph core3552) (root 8) 0 6) DegreeTwoThreeSpectrum5017.graph fusedMap3552=true := by decide +kernel
theorem certified3552 : Certified (graph core3552) (root 8) 0 6 :=
  of_native_maps core3552 DegreeTwoThreeSpectrum5533.graph DegreeTwoThreeSpectrum5017.graph
    sourceMap3552 fusedMap3552 sourceMap3552_checked fusedMap3552_checked
    DegreeTwoThreeFiniteComparisons.comparison3552
#print axioms sourceMap3552_checked
#print axioms fusedMap3552_checked
#print axioms certified3552
def sourceMap3552swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3552swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3552swap_checked : acceptsGraphIso
    (source (graph core3552) (root 8) 6 0) DegreeTwoThreeSpectrum5533.graph sourceMap3552swap=true := by decide +kernel
theorem fusedMap3552swap_checked : acceptsGraphIso
    (fused (graph core3552) (root 8) 6 0) DegreeTwoThreeSpectrum5017.graph fusedMap3552swap=true := by decide +kernel
theorem certified3552swap : Certified (graph core3552) (root 8) 6 0 :=
  of_native_maps core3552 DegreeTwoThreeSpectrum5533.graph DegreeTwoThreeSpectrum5017.graph
    sourceMap3552swap fusedMap3552swap sourceMap3552swap_checked fusedMap3552swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3552
#print axioms sourceMap3552swap_checked
#print axioms fusedMap3552swap_checked
#print axioms certified3552swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
