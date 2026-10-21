/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1431 : Family 9 := level9.get ⟨169,by decide⟩
def sourceMap1431 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1431 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1431_checked : acceptsGraphIso
    (source (graph core1431) (root 9) 0 0) DegreeOneSmallSpectrum700.graph sourceMap1431=true := by decide +kernel
theorem fusedMap1431_checked : acceptsGraphIso
    (fused (graph core1431) (root 9) 0 0) DegreeOneSmallSpectrum454.graph fusedMap1431=true := by decide +kernel
theorem certified1431 : Certified (graph core1431) (root 9) 0 0 :=
  of_native_maps core1431 DegreeOneSmallSpectrum700.graph DegreeOneSmallSpectrum454.graph
    sourceMap1431 fusedMap1431 sourceMap1431_checked fusedMap1431_checked
    DegreeOneSmallComparisons.comparison1431
#print axioms sourceMap1431_checked
#print axioms fusedMap1431_checked
#print axioms certified1431
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
