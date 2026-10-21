/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1933 : Family 10 := level10.get ⟨227,by decide⟩
def sourceMap1933 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1933 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1933_checked : acceptsGraphIso
    (source (graph core1933) (root 10) 0 0) DegreeOneSmallSpectrum1144.graph sourceMap1933=true := by decide +kernel
theorem fusedMap1933_checked : acceptsGraphIso
    (fused (graph core1933) (root 10) 0 0) DegreeOneSmallSpectrum1147.graph fusedMap1933=true := by decide +kernel
theorem certified1933 : Certified (graph core1933) (root 10) 0 0 :=
  of_native_maps core1933 DegreeOneSmallSpectrum1144.graph DegreeOneSmallSpectrum1147.graph
    sourceMap1933 fusedMap1933 sourceMap1933_checked fusedMap1933_checked
    DegreeOneSmallComparisons.comparison1933
#print axioms sourceMap1933_checked
#print axioms fusedMap1933_checked
#print axioms certified1933
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
