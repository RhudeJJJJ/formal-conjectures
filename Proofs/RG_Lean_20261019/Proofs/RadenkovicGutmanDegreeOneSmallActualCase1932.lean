/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1932 : Family 10 := level10.get ⟨226,by decide⟩
def sourceMap1932 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1932 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1932_checked : acceptsGraphIso
    (source (graph core1932) (root 10) 0 0) DegreeOneSmallSpectrum1139.graph sourceMap1932=true := by decide +kernel
theorem fusedMap1932_checked : acceptsGraphIso
    (fused (graph core1932) (root 10) 0 0) DegreeOneSmallSpectrum1142.graph fusedMap1932=true := by decide +kernel
theorem certified1932 : Certified (graph core1932) (root 10) 0 0 :=
  of_native_maps core1932 DegreeOneSmallSpectrum1139.graph DegreeOneSmallSpectrum1142.graph
    sourceMap1932 fusedMap1932 sourceMap1932_checked fusedMap1932_checked
    DegreeOneSmallComparisons.comparison1932
#print axioms sourceMap1932_checked
#print axioms fusedMap1932_checked
#print axioms certified1932
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
