/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1705 : Family 9 := level9.get ⟨486,by decide⟩
def sourceMap1705 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,8,9] (sourceLabel 9 0 0 v)
def fusedMap1705 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1705_checked : acceptsGraphIso
    (source (graph core1705) (root 9) 0 0) DegreeOneSmallSpectrum826.graph sourceMap1705=true := by decide +kernel
theorem fusedMap1705_checked : acceptsGraphIso
    (fused (graph core1705) (root 9) 0 0) DegreeOneSmallSpectrum822.graph fusedMap1705=true := by decide +kernel
theorem certified1705 : Certified (graph core1705) (root 9) 0 0 :=
  of_native_maps core1705 DegreeOneSmallSpectrum826.graph DegreeOneSmallSpectrum822.graph
    sourceMap1705 fusedMap1705 sourceMap1705_checked fusedMap1705_checked
    DegreeOneSmallComparisons.comparison1705
#print axioms sourceMap1705_checked
#print axioms fusedMap1705_checked
#print axioms certified1705
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
