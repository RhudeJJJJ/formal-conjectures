/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1050 : Family 8 := level8.get ⟨121,by decide⟩
def sourceMap1050 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,10,11,12,6,7,8,9] (sourceLabel 8 1 1 v)
def fusedMap1050 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1050_checked : acceptsGraphIso
    (source (graph core1050) (root 8) 1 1) DegreeOneSmallSpectrum1857.graph sourceMap1050=true := by decide +kernel
theorem fusedMap1050_checked : acceptsGraphIso
    (fused (graph core1050) (root 8) 1 1) DegreeOneSmallSpectrum1195.graph fusedMap1050=true := by decide +kernel
theorem certified1050 : Certified (graph core1050) (root 8) 1 1 :=
  of_native_maps core1050 DegreeOneSmallSpectrum1857.graph DegreeOneSmallSpectrum1195.graph
    sourceMap1050 fusedMap1050 sourceMap1050_checked fusedMap1050_checked
    DegreeOneSmallComparisons.comparison1050
#print axioms sourceMap1050_checked
#print axioms fusedMap1050_checked
#print axioms certified1050
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
