/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0253 : Family 5 := level5.get ⟨9,by decide⟩
def sourceMap0253 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 2 2 v)
def fusedMap0253 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap0253_checked : acceptsGraphIso
    (source (graph core0253) (root 5) 2 2) DegreeOneSmallSpectrum808.graph sourceMap0253=true := by decide +kernel
theorem fusedMap0253_checked : acceptsGraphIso
    (fused (graph core0253) (root 5) 2 2) DegreeOneSmallSpectrum380.graph fusedMap0253=true := by decide +kernel
theorem certified0253 : Certified (graph core0253) (root 5) 2 2 :=
  of_native_maps core0253 DegreeOneSmallSpectrum808.graph DegreeOneSmallSpectrum380.graph
    sourceMap0253 fusedMap0253 sourceMap0253_checked fusedMap0253_checked
    DegreeOneSmallComparisons.comparison0253
#print axioms sourceMap0253_checked
#print axioms fusedMap0253_checked
#print axioms certified0253
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
