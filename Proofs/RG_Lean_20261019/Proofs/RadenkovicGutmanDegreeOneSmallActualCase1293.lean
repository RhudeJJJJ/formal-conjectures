/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1293 : Family 9 := level9.get ⟨61,by decide⟩
def sourceMap1293 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1293 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1293_checked : acceptsGraphIso
    (source (graph core1293) (root 9) 0 0) DegreeOneSmallSpectrum466.graph sourceMap1293=true := by decide +kernel
theorem fusedMap1293_checked : acceptsGraphIso
    (fused (graph core1293) (root 9) 0 0) DegreeOneSmallSpectrum499.graph fusedMap1293=true := by decide +kernel
theorem certified1293 : Certified (graph core1293) (root 9) 0 0 :=
  of_native_maps core1293 DegreeOneSmallSpectrum466.graph DegreeOneSmallSpectrum499.graph
    sourceMap1293 fusedMap1293 sourceMap1293_checked fusedMap1293_checked
    DegreeOneSmallComparisons.comparison1293
#print axioms sourceMap1293_checked
#print axioms fusedMap1293_checked
#print axioms certified1293
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
