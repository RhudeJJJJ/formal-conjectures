/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1639 : Family 9 := level9.get ⟨386,by decide⟩
def sourceMap1639 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (sourceLabel 9 0 0 v)
def fusedMap1639 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1639_checked : acceptsGraphIso
    (source (graph core1639) (root 9) 0 0) DegreeOneSmallSpectrum746.graph sourceMap1639=true := by decide +kernel
theorem fusedMap1639_checked : acceptsGraphIso
    (fused (graph core1639) (root 9) 0 0) DegreeOneSmallSpectrum745.graph fusedMap1639=true := by decide +kernel
theorem certified1639 : Certified (graph core1639) (root 9) 0 0 :=
  of_native_maps core1639 DegreeOneSmallSpectrum746.graph DegreeOneSmallSpectrum745.graph
    sourceMap1639 fusedMap1639 sourceMap1639_checked fusedMap1639_checked
    DegreeOneSmallComparisons.comparison1639
#print axioms sourceMap1639_checked
#print axioms fusedMap1639_checked
#print axioms certified1639
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
