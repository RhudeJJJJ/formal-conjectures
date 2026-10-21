/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1621 : Family 9 := level9.get ⟨362,by decide⟩
def sourceMap1621 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (sourceLabel 9 0 0 v)
def fusedMap1621 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1621_checked : acceptsGraphIso
    (source (graph core1621) (root 9) 0 0) DegreeOneSmallSpectrum699.graph sourceMap1621=true := by decide +kernel
theorem fusedMap1621_checked : acceptsGraphIso
    (fused (graph core1621) (root 9) 0 0) DegreeOneSmallSpectrum708.graph fusedMap1621=true := by decide +kernel
theorem certified1621 : Certified (graph core1621) (root 9) 0 0 :=
  of_native_maps core1621 DegreeOneSmallSpectrum699.graph DegreeOneSmallSpectrum708.graph
    sourceMap1621 fusedMap1621 sourceMap1621_checked fusedMap1621_checked
    DegreeOneSmallComparisons.comparison1621
#print axioms sourceMap1621_checked
#print axioms fusedMap1621_checked
#print axioms certified1621
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
