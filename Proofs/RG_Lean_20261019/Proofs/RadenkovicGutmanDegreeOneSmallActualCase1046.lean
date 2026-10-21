/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1046 : Family 8 := level8.get ⟨120,by decide⟩
def sourceMap1046 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,10,11,12,6,7,8,9] (sourceLabel 8 1 1 v)
def fusedMap1046 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1046_checked : acceptsGraphIso
    (source (graph core1046) (root 8) 1 1) DegreeOneSmallSpectrum1856.graph sourceMap1046=true := by decide +kernel
theorem fusedMap1046_checked : acceptsGraphIso
    (fused (graph core1046) (root 8) 1 1) DegreeOneSmallSpectrum1189.graph fusedMap1046=true := by decide +kernel
theorem certified1046 : Certified (graph core1046) (root 8) 1 1 :=
  of_native_maps core1046 DegreeOneSmallSpectrum1856.graph DegreeOneSmallSpectrum1189.graph
    sourceMap1046 fusedMap1046 sourceMap1046_checked fusedMap1046_checked
    DegreeOneSmallComparisons.comparison1046
#print axioms sourceMap1046_checked
#print axioms fusedMap1046_checked
#print axioms certified1046
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
