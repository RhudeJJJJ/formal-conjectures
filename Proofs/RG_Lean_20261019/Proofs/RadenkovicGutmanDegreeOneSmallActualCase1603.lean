/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1603 : Family 9 := level9.get ⟨343,by decide⟩
def sourceMap1603 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,7,8] (sourceLabel 9 0 0 v)
def fusedMap1603 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1603_checked : acceptsGraphIso
    (source (graph core1603) (root 9) 0 0) DegreeOneSmallSpectrum658.graph sourceMap1603=true := by decide +kernel
theorem fusedMap1603_checked : acceptsGraphIso
    (fused (graph core1603) (root 9) 0 0) DegreeOneSmallSpectrum670.graph fusedMap1603=true := by decide +kernel
theorem certified1603 : Certified (graph core1603) (root 9) 0 0 :=
  of_native_maps core1603 DegreeOneSmallSpectrum658.graph DegreeOneSmallSpectrum670.graph
    sourceMap1603 fusedMap1603 sourceMap1603_checked fusedMap1603_checked
    DegreeOneSmallComparisons.comparison1603
#print axioms sourceMap1603_checked
#print axioms fusedMap1603_checked
#print axioms certified1603
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
