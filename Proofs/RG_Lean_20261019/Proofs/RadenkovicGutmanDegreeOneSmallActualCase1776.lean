/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1776 : Family 10 := level10.get ⟨10,by decide⟩
def sourceMap1776 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,7,0,1,2,3,4,5,6,11,12] (sourceLabel 10 0 0 v)
def fusedMap1776 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1776_checked : acceptsGraphIso
    (source (graph core1776) (root 10) 0 0) DegreeOneSmallSpectrum866.graph sourceMap1776=true := by decide +kernel
theorem fusedMap1776_checked : acceptsGraphIso
    (fused (graph core1776) (root 10) 0 0) DegreeOneSmallSpectrum870.graph fusedMap1776=true := by decide +kernel
theorem certified1776 : Certified (graph core1776) (root 10) 0 0 :=
  of_native_maps core1776 DegreeOneSmallSpectrum866.graph DegreeOneSmallSpectrum870.graph
    sourceMap1776 fusedMap1776 sourceMap1776_checked fusedMap1776_checked
    DegreeOneSmallComparisons.comparison1776
#print axioms sourceMap1776_checked
#print axioms fusedMap1776_checked
#print axioms certified1776
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
