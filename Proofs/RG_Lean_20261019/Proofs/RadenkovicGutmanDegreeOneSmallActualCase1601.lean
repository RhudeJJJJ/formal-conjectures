/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1601 : Family 9 := level9.get ⟨342,by decide⟩
def sourceMap1601 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (sourceLabel 9 0 0 v)
def fusedMap1601 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1601_checked : acceptsGraphIso
    (source (graph core1601) (root 9) 0 0) DegreeOneSmallSpectrum670.graph sourceMap1601=true := by decide +kernel
theorem fusedMap1601_checked : acceptsGraphIso
    (fused (graph core1601) (root 9) 0 0) DegreeOneSmallSpectrum669.graph fusedMap1601=true := by decide +kernel
theorem certified1601 : Certified (graph core1601) (root 9) 0 0 :=
  of_native_maps core1601 DegreeOneSmallSpectrum670.graph DegreeOneSmallSpectrum669.graph
    sourceMap1601 fusedMap1601 sourceMap1601_checked fusedMap1601_checked
    DegreeOneSmallComparisons.comparison1601
#print axioms sourceMap1601_checked
#print axioms fusedMap1601_checked
#print axioms certified1601
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
