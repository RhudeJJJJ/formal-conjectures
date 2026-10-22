/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1006 : Family 10 := level10.get ⟨1737,by decide⟩
def sourceMap1006 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap1006 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1006_checked : acceptsGraphIso
    (source (graph core1006) (root 10) 0 0) DegreeTwoThreeSpectrum1708.graph sourceMap1006=true := by decide +kernel
theorem fusedMap1006_checked : acceptsGraphIso
    (fused (graph core1006) (root 10) 0 0) DegreeOneSmallSpectrum1933.graph fusedMap1006=true := by decide +kernel
theorem certified1006 : Certified (graph core1006) (root 10) 0 0 :=
  of_native_maps core1006 DegreeTwoThreeSpectrum1708.graph DegreeOneSmallSpectrum1933.graph
    sourceMap1006 fusedMap1006 sourceMap1006_checked fusedMap1006_checked
    DegreeTwoThreeFiniteComparisons.comparison1006
#print axioms sourceMap1006_checked
#print axioms fusedMap1006_checked
#print axioms certified1006
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
