/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1806 : Family 10 := level10.get ⟨45,by decide⟩
def sourceMap1806 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1806 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1806_checked : acceptsGraphIso
    (source (graph core1806) (root 10) 0 0) DegreeOneSmallSpectrum881.graph sourceMap1806=true := by decide +kernel
theorem fusedMap1806_checked : acceptsGraphIso
    (fused (graph core1806) (root 10) 0 0) DegreeOneSmallSpectrum974.graph fusedMap1806=true := by decide +kernel
theorem certified1806 : Certified (graph core1806) (root 10) 0 0 :=
  of_native_maps core1806 DegreeOneSmallSpectrum881.graph DegreeOneSmallSpectrum974.graph
    sourceMap1806 fusedMap1806 sourceMap1806_checked fusedMap1806_checked
    DegreeOneSmallComparisons.comparison1806
#print axioms sourceMap1806_checked
#print axioms fusedMap1806_checked
#print axioms certified1806
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
