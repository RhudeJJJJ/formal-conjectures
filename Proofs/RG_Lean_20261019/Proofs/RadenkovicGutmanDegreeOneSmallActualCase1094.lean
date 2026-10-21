/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1094 : Family 8 := level8.get ⟨145,by decide⟩
def sourceMap1094 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1094 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1094_checked : acceptsGraphIso
    (source (graph core1094) (root 8) 1 1) DegreeOneSmallSpectrum1921.graph sourceMap1094=true := by decide +kernel
theorem fusedMap1094_checked : acceptsGraphIso
    (fused (graph core1094) (root 8) 1 1) DegreeOneSmallSpectrum1374.graph fusedMap1094=true := by decide +kernel
theorem certified1094 : Certified (graph core1094) (root 8) 1 1 :=
  of_native_maps core1094 DegreeOneSmallSpectrum1921.graph DegreeOneSmallSpectrum1374.graph
    sourceMap1094 fusedMap1094 sourceMap1094_checked fusedMap1094_checked
    DegreeOneSmallComparisons.comparison1094
#print axioms sourceMap1094_checked
#print axioms fusedMap1094_checked
#print axioms certified1094
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
