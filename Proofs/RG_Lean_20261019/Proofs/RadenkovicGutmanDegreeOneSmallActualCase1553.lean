/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1553 : Family 9 := level9.get ⟨287,by decide⟩
def sourceMap1553 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (sourceLabel 9 0 0 v)
def fusedMap1553 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1553_checked : acceptsGraphIso
    (source (graph core1553) (root 9) 0 0) DegreeOneSmallSpectrum586.graph sourceMap1553=true := by decide +kernel
theorem fusedMap1553_checked : acceptsGraphIso
    (fused (graph core1553) (root 9) 0 0) DegreeOneSmallSpectrum585.graph fusedMap1553=true := by decide +kernel
theorem certified1553 : Certified (graph core1553) (root 9) 0 0 :=
  of_native_maps core1553 DegreeOneSmallSpectrum586.graph DegreeOneSmallSpectrum585.graph
    sourceMap1553 fusedMap1553 sourceMap1553_checked fusedMap1553_checked
    DegreeOneSmallComparisons.comparison1553
#print axioms sourceMap1553_checked
#print axioms fusedMap1553_checked
#print axioms certified1553
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
