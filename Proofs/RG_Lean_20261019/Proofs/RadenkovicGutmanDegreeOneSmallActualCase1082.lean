/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1082 : Family 8 := level8.get ⟨141,by decide⟩
def sourceMap1082 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1082 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1082_checked : acceptsGraphIso
    (source (graph core1082) (root 8) 1 1) DegreeOneSmallSpectrum1918.graph sourceMap1082=true := by decide +kernel
theorem fusedMap1082_checked : acceptsGraphIso
    (fused (graph core1082) (root 8) 1 1) DegreeOneSmallSpectrum1353.graph fusedMap1082=true := by decide +kernel
theorem certified1082 : Certified (graph core1082) (root 8) 1 1 :=
  of_native_maps core1082 DegreeOneSmallSpectrum1918.graph DegreeOneSmallSpectrum1353.graph
    sourceMap1082 fusedMap1082 sourceMap1082_checked fusedMap1082_checked
    DegreeOneSmallComparisons.comparison1082
#print axioms sourceMap1082_checked
#print axioms fusedMap1082_checked
#print axioms certified1082
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
