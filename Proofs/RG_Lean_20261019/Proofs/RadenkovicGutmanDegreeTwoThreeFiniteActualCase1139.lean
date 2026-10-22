/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1139 : Family 8 := level8.get ⟨146,by decide⟩
def sourceMap1139 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1139 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1139_checked : acceptsGraphIso
    (source (graph core1139) (root 8) 0 2) DegreeOneSmallSpectrum1378.graph sourceMap1139=true := by decide +kernel
theorem fusedMap1139_checked : acceptsGraphIso
    (fused (graph core1139) (root 8) 0 2) DegreeOneSmallSpectrum1380.graph fusedMap1139=true := by decide +kernel
theorem certified1139 : Certified (graph core1139) (root 8) 0 2 :=
  of_native_maps core1139 DegreeOneSmallSpectrum1378.graph DegreeOneSmallSpectrum1380.graph
    sourceMap1139 fusedMap1139 sourceMap1139_checked fusedMap1139_checked
    DegreeTwoThreeFiniteComparisons.comparison1139
#print axioms sourceMap1139_checked
#print axioms fusedMap1139_checked
#print axioms certified1139
def sourceMap1139swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1139swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1139swap_checked : acceptsGraphIso
    (source (graph core1139) (root 8) 2 0) DegreeOneSmallSpectrum1378.graph sourceMap1139swap=true := by decide +kernel
theorem fusedMap1139swap_checked : acceptsGraphIso
    (fused (graph core1139) (root 8) 2 0) DegreeOneSmallSpectrum1380.graph fusedMap1139swap=true := by decide +kernel
theorem certified1139swap : Certified (graph core1139) (root 8) 2 0 :=
  of_native_maps core1139 DegreeOneSmallSpectrum1378.graph DegreeOneSmallSpectrum1380.graph
    sourceMap1139swap fusedMap1139swap sourceMap1139swap_checked fusedMap1139swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1139
#print axioms sourceMap1139swap_checked
#print axioms fusedMap1139swap_checked
#print axioms certified1139swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
