/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1227 : Family 9 := level9.get ⟨18,by decide⟩
def sourceMap1227 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,4,5] (sourceLabel 9 0 0 v)
def fusedMap1227 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1227_checked : acceptsGraphIso
    (source (graph core1227) (root 9) 0 0) DegreeOneSmallSpectrum489.graph sourceMap1227=true := by decide +kernel
theorem fusedMap1227_checked : acceptsGraphIso
    (fused (graph core1227) (root 9) 0 0) DegreeOneSmallSpectrum381.graph fusedMap1227=true := by decide +kernel
theorem certified1227 : Certified (graph core1227) (root 9) 0 0 :=
  of_native_maps core1227 DegreeOneSmallSpectrum489.graph DegreeOneSmallSpectrum381.graph
    sourceMap1227 fusedMap1227 sourceMap1227_checked fusedMap1227_checked
    DegreeOneSmallComparisons.comparison1227
#print axioms sourceMap1227_checked
#print axioms fusedMap1227_checked
#print axioms certified1227
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
