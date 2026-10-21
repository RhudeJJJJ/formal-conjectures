/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1030 : Family 8 := level8.get ⟨112,by decide⟩
def sourceMap1030 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1030 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1030_checked : acceptsGraphIso
    (source (graph core1030) (root 8) 1 1) DegreeOneSmallSpectrum1788.graph sourceMap1030=true := by decide +kernel
theorem fusedMap1030_checked : acceptsGraphIso
    (fused (graph core1030) (root 8) 1 1) DegreeOneSmallSpectrum1118.graph fusedMap1030=true := by decide +kernel
theorem certified1030 : Certified (graph core1030) (root 8) 1 1 :=
  of_native_maps core1030 DegreeOneSmallSpectrum1788.graph DegreeOneSmallSpectrum1118.graph
    sourceMap1030 fusedMap1030 sourceMap1030_checked fusedMap1030_checked
    DegreeOneSmallComparisons.comparison1030
#print axioms sourceMap1030_checked
#print axioms fusedMap1030_checked
#print axioms certified1030
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
