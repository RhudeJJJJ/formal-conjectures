/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1583 : Family 9 := level9.get ⟨325,by decide⟩
def sourceMap1583 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (sourceLabel 9 0 0 v)
def fusedMap1583 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1583_checked : acceptsGraphIso
    (source (graph core1583) (root 9) 0 0) DegreeOneSmallSpectrum618.graph sourceMap1583=true := by decide +kernel
theorem fusedMap1583_checked : acceptsGraphIso
    (fused (graph core1583) (root 9) 0 0) DegreeOneSmallSpectrum624.graph fusedMap1583=true := by decide +kernel
theorem certified1583 : Certified (graph core1583) (root 9) 0 0 :=
  of_native_maps core1583 DegreeOneSmallSpectrum618.graph DegreeOneSmallSpectrum624.graph
    sourceMap1583 fusedMap1583 sourceMap1583_checked fusedMap1583_checked
    DegreeOneSmallComparisons.comparison1583
#print axioms sourceMap1583_checked
#print axioms fusedMap1583_checked
#print axioms certified1583
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
