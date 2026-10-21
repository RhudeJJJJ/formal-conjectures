/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1006 : Family 8 := level8.get ⟨101,by decide⟩
def sourceMap1006 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 8 1 1 v)
def fusedMap1006 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1006_checked : acceptsGraphIso
    (source (graph core1006) (root 8) 1 1) DegreeOneSmallSpectrum1663.graph sourceMap1006=true := by decide +kernel
theorem fusedMap1006_checked : acceptsGraphIso
    (fused (graph core1006) (root 8) 1 1) DegreeOneSmallSpectrum1027.graph fusedMap1006=true := by decide +kernel
theorem certified1006 : Certified (graph core1006) (root 8) 1 1 :=
  of_native_maps core1006 DegreeOneSmallSpectrum1663.graph DegreeOneSmallSpectrum1027.graph
    sourceMap1006 fusedMap1006 sourceMap1006_checked fusedMap1006_checked
    DegreeOneSmallComparisons.comparison1006
#print axioms sourceMap1006_checked
#print axioms fusedMap1006_checked
#print axioms certified1006
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
