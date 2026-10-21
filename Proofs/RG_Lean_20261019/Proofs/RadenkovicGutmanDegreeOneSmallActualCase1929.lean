/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1929 : Family 10 := level10.get ⟨222,by decide⟩
def sourceMap1929 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1929 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1929_checked : acceptsGraphIso
    (source (graph core1929) (root 10) 0 0) DegreeOneSmallSpectrum1121.graph sourceMap1929=true := by decide +kernel
theorem fusedMap1929_checked : acceptsGraphIso
    (fused (graph core1929) (root 10) 0 0) DegreeOneSmallSpectrum1124.graph fusedMap1929=true := by decide +kernel
theorem certified1929 : Certified (graph core1929) (root 10) 0 0 :=
  of_native_maps core1929 DegreeOneSmallSpectrum1121.graph DegreeOneSmallSpectrum1124.graph
    sourceMap1929 fusedMap1929 sourceMap1929_checked fusedMap1929_checked
    DegreeOneSmallComparisons.comparison1929
#print axioms sourceMap1929_checked
#print axioms fusedMap1929_checked
#print axioms certified1929
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
