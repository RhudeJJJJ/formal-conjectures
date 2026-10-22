/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3472 : Family 9 := level9.get ⟨691,by decide⟩
def sourceMap3472 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3472 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3472_checked : acceptsGraphIso
    (source (graph core3472) (root 9) 0 5) DegreeTwoThreeSpectrum7065.graph sourceMap3472=true := by decide +kernel
theorem fusedMap3472_checked : acceptsGraphIso
    (fused (graph core3472) (root 9) 0 5) DegreeTwoThreeSpectrum5962.graph fusedMap3472=true := by decide +kernel
theorem certified3472 : Certified (graph core3472) (root 9) 0 5 :=
  of_native_maps core3472 DegreeTwoThreeSpectrum7065.graph DegreeTwoThreeSpectrum5962.graph
    sourceMap3472 fusedMap3472 sourceMap3472_checked fusedMap3472_checked
    DegreeTwoThreeFiniteComparisons.comparison3472
#print axioms sourceMap3472_checked
#print axioms fusedMap3472_checked
#print axioms certified3472
def sourceMap3472swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,13,14,15,16,12] (sourceLabel 9 5 0 v)
def fusedMap3472swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3472swap_checked : acceptsGraphIso
    (source (graph core3472) (root 9) 5 0) DegreeTwoThreeSpectrum7065.graph sourceMap3472swap=true := by decide +kernel
theorem fusedMap3472swap_checked : acceptsGraphIso
    (fused (graph core3472) (root 9) 5 0) DegreeTwoThreeSpectrum5962.graph fusedMap3472swap=true := by decide +kernel
theorem certified3472swap : Certified (graph core3472) (root 9) 5 0 :=
  of_native_maps core3472 DegreeTwoThreeSpectrum7065.graph DegreeTwoThreeSpectrum5962.graph
    sourceMap3472swap fusedMap3472swap sourceMap3472swap_checked fusedMap3472swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3472
#print axioms sourceMap3472swap_checked
#print axioms fusedMap3472swap_checked
#print axioms certified3472swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
