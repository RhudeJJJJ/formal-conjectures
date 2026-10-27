/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3972 : Family 7 := level7.get ⟨72,by decide⟩
def sourceMap3972 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3972 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3972_checked : acceptsGraphIso
    (source (graph core3972) (root 7) 1 5) DegreeTwoThreeSpectrum4277.graph sourceMap3972=true := by decide +kernel
theorem fusedMap3972_checked : acceptsGraphIso
    (fused (graph core3972) (root 7) 1 5) DegreeTwoThreeSpectrum3919.graph fusedMap3972=true := by decide +kernel
theorem certified3972 : Certified (graph core3972) (root 7) 1 5 :=
  of_native_maps core3972 DegreeTwoThreeSpectrum4277.graph DegreeTwoThreeSpectrum3919.graph
    sourceMap3972 fusedMap3972 sourceMap3972_checked fusedMap3972_checked
    DegreeTwoThreeFiniteComparisons.comparison3972
#print axioms sourceMap3972_checked
#print axioms fusedMap3972_checked
#print axioms certified3972
def sourceMap3972swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3972swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3972swap_checked : acceptsGraphIso
    (source (graph core3972) (root 7) 5 1) DegreeTwoThreeSpectrum4277.graph sourceMap3972swap=true := by decide +kernel
theorem fusedMap3972swap_checked : acceptsGraphIso
    (fused (graph core3972) (root 7) 5 1) DegreeTwoThreeSpectrum3919.graph fusedMap3972swap=true := by decide +kernel
theorem certified3972swap : Certified (graph core3972) (root 7) 5 1 :=
  of_native_maps core3972 DegreeTwoThreeSpectrum4277.graph DegreeTwoThreeSpectrum3919.graph
    sourceMap3972swap fusedMap3972swap sourceMap3972swap_checked fusedMap3972swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3972
#print axioms sourceMap3972swap_checked
#print axioms fusedMap3972swap_checked
#print axioms certified3972swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
