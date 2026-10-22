/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3099 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap3099 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3099 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3099_checked : acceptsGraphIso
    (source (graph core3099) (root 6) 0 5) DegreeTwoThreeSpectrum1863.graph sourceMap3099=true := by decide +kernel
theorem fusedMap3099_checked : acceptsGraphIso
    (fused (graph core3099) (root 6) 0 5) DegreeTwoThreeSpectrum1865.graph fusedMap3099=true := by decide +kernel
theorem certified3099 : Certified (graph core3099) (root 6) 0 5 :=
  of_native_maps core3099 DegreeTwoThreeSpectrum1863.graph DegreeTwoThreeSpectrum1865.graph
    sourceMap3099 fusedMap3099 sourceMap3099_checked fusedMap3099_checked
    DegreeTwoThreeFiniteComparisons.comparison3099
#print axioms sourceMap3099_checked
#print axioms fusedMap3099_checked
#print axioms certified3099
def sourceMap3099swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,8] (sourceLabel 6 5 0 v)
def fusedMap3099swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3099swap_checked : acceptsGraphIso
    (source (graph core3099) (root 6) 5 0) DegreeTwoThreeSpectrum1863.graph sourceMap3099swap=true := by decide +kernel
theorem fusedMap3099swap_checked : acceptsGraphIso
    (fused (graph core3099) (root 6) 5 0) DegreeTwoThreeSpectrum1865.graph fusedMap3099swap=true := by decide +kernel
theorem certified3099swap : Certified (graph core3099) (root 6) 5 0 :=
  of_native_maps core3099 DegreeTwoThreeSpectrum1863.graph DegreeTwoThreeSpectrum1865.graph
    sourceMap3099swap fusedMap3099swap sourceMap3099swap_checked fusedMap3099swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3099
#print axioms sourceMap3099swap_checked
#print axioms fusedMap3099swap_checked
#print axioms certified3099swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
