/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1170 : Family 8 := level8.get ⟨209,by decide⟩
def sourceMap1170 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1170 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1170_checked : acceptsGraphIso
    (source (graph core1170) (root 8) 1 1) DegreeOneSmallSpectrum1730.graph sourceMap1170=true := by decide +kernel
theorem fusedMap1170_checked : acceptsGraphIso
    (fused (graph core1170) (root 8) 1 1) DegreeOneSmallSpectrum1089.graph fusedMap1170=true := by decide +kernel
theorem certified1170 : Certified (graph core1170) (root 8) 1 1 :=
  of_native_maps core1170 DegreeOneSmallSpectrum1730.graph DegreeOneSmallSpectrum1089.graph
    sourceMap1170 fusedMap1170 sourceMap1170_checked fusedMap1170_checked
    DegreeOneSmallComparisons.comparison1170
#print axioms sourceMap1170_checked
#print axioms fusedMap1170_checked
#print axioms certified1170
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
