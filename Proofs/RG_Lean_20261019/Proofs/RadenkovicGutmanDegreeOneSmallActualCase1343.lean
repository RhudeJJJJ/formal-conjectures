/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1343 : Family 9 := level9.get ⟨97,by decide⟩
def sourceMap1343 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1343 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1343_checked : acceptsGraphIso
    (source (graph core1343) (root 9) 0 0) DegreeOneSmallSpectrum454.graph sourceMap1343=true := by decide +kernel
theorem fusedMap1343_checked : acceptsGraphIso
    (fused (graph core1343) (root 9) 0 0) DegreeOneSmallSpectrum574.graph fusedMap1343=true := by decide +kernel
theorem certified1343 : Certified (graph core1343) (root 9) 0 0 :=
  of_native_maps core1343 DegreeOneSmallSpectrum454.graph DegreeOneSmallSpectrum574.graph
    sourceMap1343 fusedMap1343 sourceMap1343_checked fusedMap1343_checked
    DegreeOneSmallComparisons.comparison1343
#print axioms sourceMap1343_checked
#print axioms fusedMap1343_checked
#print axioms certified1343
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
