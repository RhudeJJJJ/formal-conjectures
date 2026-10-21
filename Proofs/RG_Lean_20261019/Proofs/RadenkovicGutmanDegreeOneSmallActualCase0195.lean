/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0195 : Family 5 := level5.get ⟨3,by decide⟩
def sourceMap0195 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![1,0,5,6,7,4,2,3] (sourceLabel 5 0 0 v)
def fusedMap0195 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![1,0,4,5,6,7,2,3] (fusedLabel 5 0 0 v)
theorem sourceMap0195_checked : acceptsGraphIso
    (source (graph core0195) (root 5) 0 0) DegreeOneSmallSpectrum018.graph sourceMap0195=true := by decide +kernel
theorem fusedMap0195_checked : acceptsGraphIso
    (fused (graph core0195) (root 5) 0 0) DegreeOneSmallSpectrum026.graph fusedMap0195=true := by decide +kernel
theorem certified0195 : Certified (graph core0195) (root 5) 0 0 :=
  of_native_maps core0195 DegreeOneSmallSpectrum018.graph DegreeOneSmallSpectrum026.graph
    sourceMap0195 fusedMap0195 sourceMap0195_checked fusedMap0195_checked
    DegreeOneSmallComparisons.comparison0195
#print axioms sourceMap0195_checked
#print axioms fusedMap0195_checked
#print axioms certified0195
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
