/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1960 : Family 10 := level10.get ⟨267,by decide⟩
def sourceMap1960 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap1960 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,10,11,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap1960_checked : acceptsGraphIso
    (source (graph core1960) (root 10) 0 0) DegreeOneSmallSpectrum1098.graph sourceMap1960=true := by decide +kernel
theorem fusedMap1960_checked : acceptsGraphIso
    (fused (graph core1960) (root 10) 0 0) DegreeOneSmallSpectrum1282.graph fusedMap1960=true := by decide +kernel
theorem certified1960 : Certified (graph core1960) (root 10) 0 0 :=
  of_native_maps core1960 DegreeOneSmallSpectrum1098.graph DegreeOneSmallSpectrum1282.graph
    sourceMap1960 fusedMap1960 sourceMap1960_checked fusedMap1960_checked
    DegreeOneSmallComparisons.comparison1960
#print axioms sourceMap1960_checked
#print axioms fusedMap1960_checked
#print axioms certified1960
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
