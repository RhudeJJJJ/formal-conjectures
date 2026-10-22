/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1187 : Family 8 := level8.get ⟨257,by decide⟩
def sourceMap1187 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,7,8,9,10,11,12,4,5,6] (sourceLabel 8 0 2 v)
def fusedMap1187 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1187_checked : acceptsGraphIso
    (source (graph core1187) (root 8) 0 2) DegreeOneSmallSpectrum1977.graph sourceMap1187=true := by decide +kernel
theorem fusedMap1187_checked : acceptsGraphIso
    (fused (graph core1187) (root 8) 0 2) DegreeOneSmallSpectrum1464.graph fusedMap1187=true := by decide +kernel
theorem certified1187 : Certified (graph core1187) (root 8) 0 2 :=
  of_native_maps core1187 DegreeOneSmallSpectrum1977.graph DegreeOneSmallSpectrum1464.graph
    sourceMap1187 fusedMap1187 sourceMap1187_checked fusedMap1187_checked
    DegreeTwoThreeFiniteComparisons.comparison1187
#print axioms sourceMap1187_checked
#print axioms fusedMap1187_checked
#print axioms certified1187
def sourceMap1187swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,7,8,9,10,11,4,5,6,12] (sourceLabel 8 2 0 v)
def fusedMap1187swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1187swap_checked : acceptsGraphIso
    (source (graph core1187) (root 8) 2 0) DegreeOneSmallSpectrum1977.graph sourceMap1187swap=true := by decide +kernel
theorem fusedMap1187swap_checked : acceptsGraphIso
    (fused (graph core1187) (root 8) 2 0) DegreeOneSmallSpectrum1464.graph fusedMap1187swap=true := by decide +kernel
theorem certified1187swap : Certified (graph core1187) (root 8) 2 0 :=
  of_native_maps core1187 DegreeOneSmallSpectrum1977.graph DegreeOneSmallSpectrum1464.graph
    sourceMap1187swap fusedMap1187swap sourceMap1187swap_checked fusedMap1187swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1187
#print axioms sourceMap1187swap_checked
#print axioms fusedMap1187swap_checked
#print axioms certified1187swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
