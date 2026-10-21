/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0237 : Family 5 := level5.get ⟨8,by decide⟩
def sourceMap0237 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4] (sourceLabel 5 1 1 v)
def fusedMap0237 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap0237_checked : acceptsGraphIso
    (source (graph core0237) (root 5) 1 1) DegreeOneSmallSpectrum134.graph sourceMap0237=true := by decide +kernel
theorem fusedMap0237_checked : acceptsGraphIso
    (fused (graph core0237) (root 5) 1 1) DegreeOneSmallSpectrum081.graph fusedMap0237=true := by decide +kernel
theorem certified0237 : Certified (graph core0237) (root 5) 1 1 :=
  of_native_maps core0237 DegreeOneSmallSpectrum134.graph DegreeOneSmallSpectrum081.graph
    sourceMap0237 fusedMap0237 sourceMap0237_checked fusedMap0237_checked
    DegreeOneSmallComparisons.comparison0237
#print axioms sourceMap0237_checked
#print axioms fusedMap0237_checked
#print axioms certified0237
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
