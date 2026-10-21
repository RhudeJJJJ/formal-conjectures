/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0213 : Family 5 := level5.get ⟨5,by decide⟩
def sourceMap0213 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9] (sourceLabel 5 1 1 v)
def fusedMap0213 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap0213_checked : acceptsGraphIso
    (source (graph core0213) (root 5) 1 1) DegreeOneSmallSpectrum104.graph sourceMap0213=true := by decide +kernel
theorem fusedMap0213_checked : acceptsGraphIso
    (fused (graph core0213) (root 5) 1 1) DegreeOneSmallSpectrum074.graph fusedMap0213=true := by decide +kernel
theorem certified0213 : Certified (graph core0213) (root 5) 1 1 :=
  of_native_maps core0213 DegreeOneSmallSpectrum104.graph DegreeOneSmallSpectrum074.graph
    sourceMap0213 fusedMap0213 sourceMap0213_checked fusedMap0213_checked
    DegreeOneSmallComparisons.comparison0213
#print axioms sourceMap0213_checked
#print axioms fusedMap0213_checked
#print axioms certified0213
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
