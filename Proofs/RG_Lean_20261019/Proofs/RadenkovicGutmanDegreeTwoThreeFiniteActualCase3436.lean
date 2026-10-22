/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3436 : Family 9 := level9.get ⟨578,by decide⟩
def sourceMap3436 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3436 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3436_checked : acceptsGraphIso
    (source (graph core3436) (root 9) 0 5) DegreeTwoThreeSpectrum6120.graph sourceMap3436=true := by decide +kernel
theorem fusedMap3436_checked : acceptsGraphIso
    (fused (graph core3436) (root 9) 0 5) DegreeTwoThreeSpectrum6121.graph fusedMap3436=true := by decide +kernel
theorem certified3436 : Certified (graph core3436) (root 9) 0 5 :=
  of_native_maps core3436 DegreeTwoThreeSpectrum6120.graph DegreeTwoThreeSpectrum6121.graph
    sourceMap3436 fusedMap3436 sourceMap3436_checked fusedMap3436_checked
    DegreeTwoThreeFiniteComparisons.comparison3436
#print axioms sourceMap3436_checked
#print axioms fusedMap3436_checked
#print axioms certified3436
def sourceMap3436swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3436swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3436swap_checked : acceptsGraphIso
    (source (graph core3436) (root 9) 5 0) DegreeTwoThreeSpectrum6120.graph sourceMap3436swap=true := by decide +kernel
theorem fusedMap3436swap_checked : acceptsGraphIso
    (fused (graph core3436) (root 9) 5 0) DegreeTwoThreeSpectrum6121.graph fusedMap3436swap=true := by decide +kernel
theorem certified3436swap : Certified (graph core3436) (root 9) 5 0 :=
  of_native_maps core3436 DegreeTwoThreeSpectrum6120.graph DegreeTwoThreeSpectrum6121.graph
    sourceMap3436swap fusedMap3436swap sourceMap3436swap_checked fusedMap3436swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3436
#print axioms sourceMap3436swap_checked
#print axioms fusedMap3436swap_checked
#print axioms certified3436swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
