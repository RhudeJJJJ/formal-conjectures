/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1054 : Family 8 := level8.get ⟨122,by decide⟩
def sourceMap1054 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,10,11,12,6,7,8,9] (sourceLabel 8 1 1 v)
def fusedMap1054 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1054_checked : acceptsGraphIso
    (source (graph core1054) (root 8) 1 1) DegreeOneSmallSpectrum1858.graph sourceMap1054=true := by decide +kernel
theorem fusedMap1054_checked : acceptsGraphIso
    (fused (graph core1054) (root 8) 1 1) DegreeOneSmallSpectrum1201.graph fusedMap1054=true := by decide +kernel
theorem certified1054 : Certified (graph core1054) (root 8) 1 1 :=
  of_native_maps core1054 DegreeOneSmallSpectrum1858.graph DegreeOneSmallSpectrum1201.graph
    sourceMap1054 fusedMap1054 sourceMap1054_checked fusedMap1054_checked
    DegreeOneSmallComparisons.comparison1054
#print axioms sourceMap1054_checked
#print axioms fusedMap1054_checked
#print axioms certified1054
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
