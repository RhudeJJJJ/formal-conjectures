/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1349 : Family 9 := level9.get ⟨101,by decide⟩
def sourceMap1349 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1349 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1349_checked : acceptsGraphIso
    (source (graph core1349) (root 9) 0 0) DegreeOneSmallSpectrum455.graph sourceMap1349=true := by decide +kernel
theorem fusedMap1349_checked : acceptsGraphIso
    (fused (graph core1349) (root 9) 0 0) DegreeOneSmallSpectrum580.graph fusedMap1349=true := by decide +kernel
theorem certified1349 : Certified (graph core1349) (root 9) 0 0 :=
  of_native_maps core1349 DegreeOneSmallSpectrum455.graph DegreeOneSmallSpectrum580.graph
    sourceMap1349 fusedMap1349 sourceMap1349_checked fusedMap1349_checked
    DegreeOneSmallComparisons.comparison1349
#print axioms sourceMap1349_checked
#print axioms fusedMap1349_checked
#print axioms certified1349
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
