/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3577 : Family 8 := level8.get ⟨129,by decide⟩
def sourceMap3577 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3577 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3577_checked : acceptsGraphIso
    (source (graph core3577) (root 8) 0 6) DegreeTwoThreeSpectrum5369.graph sourceMap3577=true := by decide +kernel
theorem fusedMap3577_checked : acceptsGraphIso
    (fused (graph core3577) (root 8) 0 6) DegreeTwoThreeSpectrum5371.graph fusedMap3577=true := by decide +kernel
theorem certified3577 : Certified (graph core3577) (root 8) 0 6 :=
  of_native_maps core3577 DegreeTwoThreeSpectrum5369.graph DegreeTwoThreeSpectrum5371.graph
    sourceMap3577 fusedMap3577 sourceMap3577_checked fusedMap3577_checked
    DegreeTwoThreeFiniteComparisons.comparison3577
#print axioms sourceMap3577_checked
#print axioms fusedMap3577_checked
#print axioms certified3577
def sourceMap3577swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3577swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3577swap_checked : acceptsGraphIso
    (source (graph core3577) (root 8) 6 0) DegreeTwoThreeSpectrum5369.graph sourceMap3577swap=true := by decide +kernel
theorem fusedMap3577swap_checked : acceptsGraphIso
    (fused (graph core3577) (root 8) 6 0) DegreeTwoThreeSpectrum5371.graph fusedMap3577swap=true := by decide +kernel
theorem certified3577swap : Certified (graph core3577) (root 8) 6 0 :=
  of_native_maps core3577 DegreeTwoThreeSpectrum5369.graph DegreeTwoThreeSpectrum5371.graph
    sourceMap3577swap fusedMap3577swap sourceMap3577swap_checked fusedMap3577swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3577
#print axioms sourceMap3577swap_checked
#print axioms fusedMap3577swap_checked
#print axioms certified3577swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
