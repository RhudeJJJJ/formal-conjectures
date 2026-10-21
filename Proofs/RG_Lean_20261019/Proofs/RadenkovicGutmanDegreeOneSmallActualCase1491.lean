/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1491 : Family 9 := level9.get ⟨222,by decide⟩
def sourceMap1491 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1491 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1491_checked : acceptsGraphIso
    (source (graph core1491) (root 9) 0 0) DegreeOneSmallSpectrum725.graph sourceMap1491=true := by decide +kernel
theorem fusedMap1491_checked : acceptsGraphIso
    (fused (graph core1491) (root 9) 0 0) DegreeOneSmallSpectrum532.graph fusedMap1491=true := by decide +kernel
theorem certified1491 : Certified (graph core1491) (root 9) 0 0 :=
  of_native_maps core1491 DegreeOneSmallSpectrum725.graph DegreeOneSmallSpectrum532.graph
    sourceMap1491 fusedMap1491 sourceMap1491_checked fusedMap1491_checked
    DegreeOneSmallComparisons.comparison1491
#print axioms sourceMap1491_checked
#print axioms fusedMap1491_checked
#print axioms certified1491
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
