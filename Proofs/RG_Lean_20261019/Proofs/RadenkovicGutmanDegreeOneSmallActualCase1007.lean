/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1007 : Family 8 := level8.get ⟨103,by decide⟩
def sourceMap1007 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,5,0,1,2,3,4,9,10,7,8] (sourceLabel 8 0 0 v)
def fusedMap1007 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap1007_checked : acceptsGraphIso
    (source (graph core1007) (root 8) 0 0) DegreeOneSmallSpectrum259.graph sourceMap1007=true := by decide +kernel
theorem fusedMap1007_checked : acceptsGraphIso
    (fused (graph core1007) (root 8) 0 0) DegreeOneSmallSpectrum265.graph fusedMap1007=true := by decide +kernel
theorem certified1007 : Certified (graph core1007) (root 8) 0 0 :=
  of_native_maps core1007 DegreeOneSmallSpectrum259.graph DegreeOneSmallSpectrum265.graph
    sourceMap1007 fusedMap1007 sourceMap1007_checked fusedMap1007_checked
    DegreeOneSmallComparisons.comparison1007
#print axioms sourceMap1007_checked
#print axioms fusedMap1007_checked
#print axioms certified1007
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
