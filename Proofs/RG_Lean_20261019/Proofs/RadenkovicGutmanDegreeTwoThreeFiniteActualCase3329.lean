/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3329 : Family 9 := level9.get ⟨310,by decide⟩
def sourceMap3329 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3329 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3329_checked : acceptsGraphIso
    (source (graph core3329) (root 9) 0 5) DegreeTwoThreeSpectrum5921.graph sourceMap3329=true := by decide +kernel
theorem fusedMap3329_checked : acceptsGraphIso
    (fused (graph core3329) (root 9) 0 5) DegreeTwoThreeSpectrum5922.graph fusedMap3329=true := by decide +kernel
theorem certified3329 : Certified (graph core3329) (root 9) 0 5 :=
  of_native_maps core3329 DegreeTwoThreeSpectrum5921.graph DegreeTwoThreeSpectrum5922.graph
    sourceMap3329 fusedMap3329 sourceMap3329_checked fusedMap3329_checked
    DegreeTwoThreeFiniteComparisons.comparison3329
#print axioms sourceMap3329_checked
#print axioms fusedMap3329_checked
#print axioms certified3329
def sourceMap3329swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3329swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3329swap_checked : acceptsGraphIso
    (source (graph core3329) (root 9) 5 0) DegreeTwoThreeSpectrum5921.graph sourceMap3329swap=true := by decide +kernel
theorem fusedMap3329swap_checked : acceptsGraphIso
    (fused (graph core3329) (root 9) 5 0) DegreeTwoThreeSpectrum5922.graph fusedMap3329swap=true := by decide +kernel
theorem certified3329swap : Certified (graph core3329) (root 9) 5 0 :=
  of_native_maps core3329 DegreeTwoThreeSpectrum5921.graph DegreeTwoThreeSpectrum5922.graph
    sourceMap3329swap fusedMap3329swap sourceMap3329swap_checked fusedMap3329swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3329
#print axioms sourceMap3329swap_checked
#print axioms fusedMap3329swap_checked
#print axioms certified3329swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
