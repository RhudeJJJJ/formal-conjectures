/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1922 : Family 10 := level10.get ⟨211,by decide⟩
def sourceMap1922 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap1922 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1922_checked : acceptsGraphIso
    (source (graph core1922) (root 10) 0 0) DegreeOneSmallSpectrum1061.graph sourceMap1922=true := by decide +kernel
theorem fusedMap1922_checked : acceptsGraphIso
    (fused (graph core1922) (root 10) 0 0) DegreeOneSmallSpectrum1079.graph fusedMap1922=true := by decide +kernel
theorem certified1922 : Certified (graph core1922) (root 10) 0 0 :=
  of_native_maps core1922 DegreeOneSmallSpectrum1061.graph DegreeOneSmallSpectrum1079.graph
    sourceMap1922 fusedMap1922 sourceMap1922_checked fusedMap1922_checked
    DegreeOneSmallComparisons.comparison1922
#print axioms sourceMap1922_checked
#print axioms fusedMap1922_checked
#print axioms certified1922
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
