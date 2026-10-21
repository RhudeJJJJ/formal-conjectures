/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0822 : Family 8 := level8.get ⟨25,by decide⟩
def sourceMap0822 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0822 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0822_checked : acceptsGraphIso
    (source (graph core0822) (root 8) 1 1) DegreeOneSmallSpectrum1347.graph sourceMap0822=true := by decide +kernel
theorem fusedMap0822_checked : acceptsGraphIso
    (fused (graph core0822) (root 8) 1 1) DegreeOneSmallSpectrum971.graph fusedMap0822=true := by decide +kernel
theorem certified0822 : Certified (graph core0822) (root 8) 1 1 :=
  of_native_maps core0822 DegreeOneSmallSpectrum1347.graph DegreeOneSmallSpectrum971.graph
    sourceMap0822 fusedMap0822 sourceMap0822_checked fusedMap0822_checked
    DegreeOneSmallComparisons.comparison0822
#print axioms sourceMap0822_checked
#print axioms fusedMap0822_checked
#print axioms certified0822
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
