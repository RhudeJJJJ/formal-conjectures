/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1091 : Family 8 := level8.get ⟨145,by decide⟩
def sourceMap1091 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,4,5,2,3] (sourceLabel 8 0 0 v)
def fusedMap1091 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap1091_checked : acceptsGraphIso
    (source (graph core1091) (root 8) 0 0) DegreeOneSmallSpectrum289.graph sourceMap1091=true := by decide +kernel
theorem fusedMap1091_checked : acceptsGraphIso
    (fused (graph core1091) (root 8) 0 0) DegreeOneSmallSpectrum338.graph fusedMap1091=true := by decide +kernel
theorem certified1091 : Certified (graph core1091) (root 8) 0 0 :=
  of_native_maps core1091 DegreeOneSmallSpectrum289.graph DegreeOneSmallSpectrum338.graph
    sourceMap1091 fusedMap1091 sourceMap1091_checked fusedMap1091_checked
    DegreeOneSmallComparisons.comparison1091
#print axioms sourceMap1091_checked
#print axioms fusedMap1091_checked
#print axioms certified1091
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
