/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1022 : Family 8 := level8.get ⟨109,by decide⟩
def sourceMap1022 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1022 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1022_checked : acceptsGraphIso
    (source (graph core1022) (root 8) 1 1) DegreeOneSmallSpectrum1749.graph sourceMap1022=true := by decide +kernel
theorem fusedMap1022_checked : acceptsGraphIso
    (fused (graph core1022) (root 8) 1 1) DegreeOneSmallSpectrum1095.graph fusedMap1022=true := by decide +kernel
theorem certified1022 : Certified (graph core1022) (root 8) 1 1 :=
  of_native_maps core1022 DegreeOneSmallSpectrum1749.graph DegreeOneSmallSpectrum1095.graph
    sourceMap1022 fusedMap1022 sourceMap1022_checked fusedMap1022_checked
    DegreeOneSmallComparisons.comparison1022
#print axioms sourceMap1022_checked
#print axioms fusedMap1022_checked
#print axioms certified1022
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
