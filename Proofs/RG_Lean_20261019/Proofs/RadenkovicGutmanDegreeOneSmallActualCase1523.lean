/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1523 : Family 9 := level9.get ⟨255,by decide⟩
def sourceMap1523 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1523 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1523_checked : acceptsGraphIso
    (source (graph core1523) (root 9) 0 0) DegreeOneSmallSpectrum767.graph sourceMap1523=true := by decide +kernel
theorem fusedMap1523_checked : acceptsGraphIso
    (fused (graph core1523) (root 9) 0 0) DegreeOneSmallSpectrum565.graph fusedMap1523=true := by decide +kernel
theorem certified1523 : Certified (graph core1523) (root 9) 0 0 :=
  of_native_maps core1523 DegreeOneSmallSpectrum767.graph DegreeOneSmallSpectrum565.graph
    sourceMap1523 fusedMap1523 sourceMap1523_checked fusedMap1523_checked
    DegreeOneSmallComparisons.comparison1523
#print axioms sourceMap1523_checked
#print axioms fusedMap1523_checked
#print axioms certified1523
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
