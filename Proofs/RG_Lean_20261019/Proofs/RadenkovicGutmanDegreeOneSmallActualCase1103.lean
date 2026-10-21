/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1103 : Family 8 := level8.get ⟨151,by decide⟩
def sourceMap1103 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,4,5,6,2,3] (sourceLabel 8 0 0 v)
def fusedMap1103 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap1103_checked : acceptsGraphIso
    (source (graph core1103) (root 8) 0 0) DegreeOneSmallSpectrum274.graph sourceMap1103=true := by decide +kernel
theorem fusedMap1103_checked : acceptsGraphIso
    (fused (graph core1103) (root 8) 0 0) DegreeOneSmallSpectrum343.graph fusedMap1103=true := by decide +kernel
theorem certified1103 : Certified (graph core1103) (root 8) 0 0 :=
  of_native_maps core1103 DegreeOneSmallSpectrum274.graph DegreeOneSmallSpectrum343.graph
    sourceMap1103 fusedMap1103 sourceMap1103_checked fusedMap1103_checked
    DegreeOneSmallComparisons.comparison1103
#print axioms sourceMap1103_checked
#print axioms fusedMap1103_checked
#print axioms certified1103
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
