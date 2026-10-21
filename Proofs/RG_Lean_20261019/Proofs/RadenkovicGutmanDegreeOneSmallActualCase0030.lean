/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0030 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0030 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 1) → Fin 5 :=
  fun v => ![0,3,4,1,2] (sourceLabel 2 0 0 v)
def fusedMap0030 : (Vertices 2 ⊕ Fin 2) → Fin 5 :=
  fun v => ![0,1,2,3,4] (fusedLabel 2 0 0 v)
theorem sourceMap0030_checked : acceptsGraphIso
    (source (graph core0030) (root 2) 0 0) DegreeOneSmallSpectrum002.graph sourceMap0030=true := by decide +kernel
theorem fusedMap0030_checked : acceptsGraphIso
    (fused (graph core0030) (root 2) 0 0) DegreeOneSmallSpectrum003.graph fusedMap0030=true := by decide +kernel
theorem certified0030 : Certified (graph core0030) (root 2) 0 0 :=
  of_native_maps core0030 DegreeOneSmallSpectrum002.graph DegreeOneSmallSpectrum003.graph
    sourceMap0030 fusedMap0030 sourceMap0030_checked fusedMap0030_checked
    DegreeOneSmallComparisons.comparison0030
#print axioms sourceMap0030_checked
#print axioms fusedMap0030_checked
#print axioms certified0030
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
