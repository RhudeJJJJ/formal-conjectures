/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1800 : Family 10 := level10.get ⟨37,by decide⟩
def sourceMap1800 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1800 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1800_checked : acceptsGraphIso
    (source (graph core1800) (root 10) 0 0) DegreeOneSmallSpectrum878.graph sourceMap1800=true := by decide +kernel
theorem fusedMap1800_checked : acceptsGraphIso
    (fused (graph core1800) (root 10) 0 0) DegreeOneSmallSpectrum965.graph fusedMap1800=true := by decide +kernel
theorem certified1800 : Certified (graph core1800) (root 10) 0 0 :=
  of_native_maps core1800 DegreeOneSmallSpectrum878.graph DegreeOneSmallSpectrum965.graph
    sourceMap1800 fusedMap1800 sourceMap1800_checked fusedMap1800_checked
    DegreeOneSmallComparisons.comparison1800
#print axioms sourceMap1800_checked
#print axioms fusedMap1800_checked
#print axioms certified1800
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
