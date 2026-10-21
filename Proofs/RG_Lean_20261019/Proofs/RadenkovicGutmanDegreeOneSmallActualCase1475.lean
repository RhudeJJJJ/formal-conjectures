/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1475 : Family 9 := level9.get ⟨209,by decide⟩
def sourceMap1475 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1475 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1475_checked : acceptsGraphIso
    (source (graph core1475) (root 9) 0 0) DegreeOneSmallSpectrum723.graph sourceMap1475=true := by decide +kernel
theorem fusedMap1475_checked : acceptsGraphIso
    (fused (graph core1475) (root 9) 0 0) DegreeOneSmallSpectrum516.graph fusedMap1475=true := by decide +kernel
theorem certified1475 : Certified (graph core1475) (root 9) 0 0 :=
  of_native_maps core1475 DegreeOneSmallSpectrum723.graph DegreeOneSmallSpectrum516.graph
    sourceMap1475 fusedMap1475 sourceMap1475_checked fusedMap1475_checked
    DegreeOneSmallComparisons.comparison1475
#print axioms sourceMap1475_checked
#print axioms fusedMap1475_checked
#print axioms certified1475
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
