/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1609 : Family 9 := level9.get ⟨354,by decide⟩
def sourceMap1609 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (sourceLabel 9 0 0 v)
def fusedMap1609 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1609_checked : acceptsGraphIso
    (source (graph core1609) (root 9) 0 0) DegreeOneSmallSpectrum675.graph sourceMap1609=true := by decide +kernel
theorem fusedMap1609_checked : acceptsGraphIso
    (fused (graph core1609) (root 9) 0 0) DegreeOneSmallSpectrum677.graph fusedMap1609=true := by decide +kernel
theorem certified1609 : Certified (graph core1609) (root 9) 0 0 :=
  of_native_maps core1609 DegreeOneSmallSpectrum675.graph DegreeOneSmallSpectrum677.graph
    sourceMap1609 fusedMap1609 sourceMap1609_checked fusedMap1609_checked
    DegreeOneSmallComparisons.comparison1609
#print axioms sourceMap1609_checked
#print axioms fusedMap1609_checked
#print axioms certified1609
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
