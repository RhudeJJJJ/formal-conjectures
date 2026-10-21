/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1075 : Family 8 := level8.get ⟨137,by decide⟩
def sourceMap1075 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,4,5,2,3] (sourceLabel 8 0 0 v)
def fusedMap1075 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap1075_checked : acceptsGraphIso
    (source (graph core1075) (root 8) 0 0) DegreeOneSmallSpectrum288.graph sourceMap1075=true := by decide +kernel
theorem fusedMap1075_checked : acceptsGraphIso
    (fused (graph core1075) (root 8) 0 0) DegreeOneSmallSpectrum330.graph fusedMap1075=true := by decide +kernel
theorem certified1075 : Certified (graph core1075) (root 8) 0 0 :=
  of_native_maps core1075 DegreeOneSmallSpectrum288.graph DegreeOneSmallSpectrum330.graph
    sourceMap1075 fusedMap1075 sourceMap1075_checked fusedMap1075_checked
    DegreeOneSmallComparisons.comparison1075
#print axioms sourceMap1075_checked
#print axioms fusedMap1075_checked
#print axioms certified1075
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
