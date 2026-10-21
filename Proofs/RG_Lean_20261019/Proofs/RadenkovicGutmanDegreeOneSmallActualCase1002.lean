/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1002 : Family 8 := level8.get ⟨100,by decide⟩
def sourceMap1002 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1002 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1002_checked : acceptsGraphIso
    (source (graph core1002) (root 8) 1 1) DegreeOneSmallSpectrum1651.graph sourceMap1002=true := by decide +kernel
theorem fusedMap1002_checked : acceptsGraphIso
    (fused (graph core1002) (root 8) 1 1) DegreeOneSmallSpectrum1021.graph fusedMap1002=true := by decide +kernel
theorem certified1002 : Certified (graph core1002) (root 8) 1 1 :=
  of_native_maps core1002 DegreeOneSmallSpectrum1651.graph DegreeOneSmallSpectrum1021.graph
    sourceMap1002 fusedMap1002 sourceMap1002_checked fusedMap1002_checked
    DegreeOneSmallComparisons.comparison1002
#print axioms sourceMap1002_checked
#print axioms fusedMap1002_checked
#print axioms certified1002
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
