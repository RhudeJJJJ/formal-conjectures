/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1473 : Family 9 := level9.get ⟨208,by decide⟩
def sourceMap1473 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1473 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1473_checked : acceptsGraphIso
    (source (graph core1473) (root 9) 0 0) DegreeOneSmallSpectrum703.graph sourceMap1473=true := by decide +kernel
theorem fusedMap1473_checked : acceptsGraphIso
    (fused (graph core1473) (root 9) 0 0) DegreeOneSmallSpectrum515.graph fusedMap1473=true := by decide +kernel
theorem certified1473 : Certified (graph core1473) (root 9) 0 0 :=
  of_native_maps core1473 DegreeOneSmallSpectrum703.graph DegreeOneSmallSpectrum515.graph
    sourceMap1473 fusedMap1473 sourceMap1473_checked fusedMap1473_checked
    DegreeOneSmallComparisons.comparison1473
#print axioms sourceMap1473_checked
#print axioms fusedMap1473_checked
#print axioms certified1473
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
