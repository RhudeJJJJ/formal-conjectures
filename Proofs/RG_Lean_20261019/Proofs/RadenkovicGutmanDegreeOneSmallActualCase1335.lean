/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1335 : Family 9 := level9.get ⟨93,by decide⟩
def sourceMap1335 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1335 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1335_checked : acceptsGraphIso
    (source (graph core1335) (root 9) 0 0) DegreeOneSmallSpectrum491.graph sourceMap1335=true := by decide +kernel
theorem fusedMap1335_checked : acceptsGraphIso
    (fused (graph core1335) (root 9) 0 0) DegreeOneSmallSpectrum563.graph fusedMap1335=true := by decide +kernel
theorem certified1335 : Certified (graph core1335) (root 9) 0 0 :=
  of_native_maps core1335 DegreeOneSmallSpectrum491.graph DegreeOneSmallSpectrum563.graph
    sourceMap1335 fusedMap1335 sourceMap1335_checked fusedMap1335_checked
    DegreeOneSmallComparisons.comparison1335
#print axioms sourceMap1335_checked
#print axioms fusedMap1335_checked
#print axioms certified1335
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
