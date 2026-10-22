/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1016 : Family 10 := level10.get ⟨1801,by decide⟩
def sourceMap1016 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap1016 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1016_checked : acceptsGraphIso
    (source (graph core1016) (root 10) 0 0) DegreeTwoThreeSpectrum1680.graph sourceMap1016=true := by decide +kernel
theorem fusedMap1016_checked : acceptsGraphIso
    (fused (graph core1016) (root 10) 0 0) DegreeOneSmallSpectrum1990.graph fusedMap1016=true := by decide +kernel
theorem certified1016 : Certified (graph core1016) (root 10) 0 0 :=
  of_native_maps core1016 DegreeTwoThreeSpectrum1680.graph DegreeOneSmallSpectrum1990.graph
    sourceMap1016 fusedMap1016 sourceMap1016_checked fusedMap1016_checked
    DegreeTwoThreeFiniteComparisons.comparison1016
#print axioms sourceMap1016_checked
#print axioms fusedMap1016_checked
#print axioms certified1016
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
