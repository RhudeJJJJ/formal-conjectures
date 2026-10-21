/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1167 : Family 8 := level8.get ⟨209,by decide⟩
def sourceMap1167 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (sourceLabel 8 0 0 v)
def fusedMap1167 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1167_checked : acceptsGraphIso
    (source (graph core1167) (root 8) 0 0) DegreeOneSmallSpectrum363.graph sourceMap1167=true := by decide +kernel
theorem fusedMap1167_checked : acceptsGraphIso
    (fused (graph core1167) (root 8) 0 0) DegreeOneSmallSpectrum271.graph fusedMap1167=true := by decide +kernel
theorem certified1167 : Certified (graph core1167) (root 8) 0 0 :=
  of_native_maps core1167 DegreeOneSmallSpectrum363.graph DegreeOneSmallSpectrum271.graph
    sourceMap1167 fusedMap1167 sourceMap1167_checked fusedMap1167_checked
    DegreeOneSmallComparisons.comparison1167
#print axioms sourceMap1167_checked
#print axioms fusedMap1167_checked
#print axioms certified1167
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
