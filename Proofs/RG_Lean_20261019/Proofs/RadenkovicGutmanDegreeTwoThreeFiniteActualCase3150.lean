/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3150 : Family 8 := level8.get ⟨50,by decide⟩
def sourceMap3150 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3150 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3150_checked : acceptsGraphIso
    (source (graph core3150) (root 8) 0 5) DegreeTwoThreeSpectrum3967.graph sourceMap3150=true := by decide +kernel
theorem fusedMap3150_checked : acceptsGraphIso
    (fused (graph core3150) (root 8) 0 5) DegreeTwoThreeSpectrum3968.graph fusedMap3150=true := by decide +kernel
theorem certified3150 : Certified (graph core3150) (root 8) 0 5 :=
  of_native_maps core3150 DegreeTwoThreeSpectrum3967.graph DegreeTwoThreeSpectrum3968.graph
    sourceMap3150 fusedMap3150 sourceMap3150_checked fusedMap3150_checked
    DegreeTwoThreeFiniteComparisons.comparison3150
#print axioms sourceMap3150_checked
#print axioms fusedMap3150_checked
#print axioms certified3150
def sourceMap3150swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3150swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3150swap_checked : acceptsGraphIso
    (source (graph core3150) (root 8) 5 0) DegreeTwoThreeSpectrum3967.graph sourceMap3150swap=true := by decide +kernel
theorem fusedMap3150swap_checked : acceptsGraphIso
    (fused (graph core3150) (root 8) 5 0) DegreeTwoThreeSpectrum3968.graph fusedMap3150swap=true := by decide +kernel
theorem certified3150swap : Certified (graph core3150) (root 8) 5 0 :=
  of_native_maps core3150 DegreeTwoThreeSpectrum3967.graph DegreeTwoThreeSpectrum3968.graph
    sourceMap3150swap fusedMap3150swap sourceMap3150swap_checked fusedMap3150swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3150
#print axioms sourceMap3150swap_checked
#print axioms fusedMap3150swap_checked
#print axioms certified3150swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
