/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1118 : Family 8 := level8.get ⟨163,by decide⟩
def sourceMap1118 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1118 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1118_checked : acceptsGraphIso
    (source (graph core1118) (root 8) 1 1) DegreeOneSmallSpectrum1927.graph sourceMap1118=true := by decide +kernel
theorem fusedMap1118_checked : acceptsGraphIso
    (fused (graph core1118) (root 8) 1 1) DegreeOneSmallSpectrum1467.graph fusedMap1118=true := by decide +kernel
theorem certified1118 : Certified (graph core1118) (root 8) 1 1 :=
  of_native_maps core1118 DegreeOneSmallSpectrum1927.graph DegreeOneSmallSpectrum1467.graph
    sourceMap1118 fusedMap1118 sourceMap1118_checked fusedMap1118_checked
    DegreeOneSmallComparisons.comparison1118
#print axioms sourceMap1118_checked
#print axioms fusedMap1118_checked
#print axioms certified1118
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
