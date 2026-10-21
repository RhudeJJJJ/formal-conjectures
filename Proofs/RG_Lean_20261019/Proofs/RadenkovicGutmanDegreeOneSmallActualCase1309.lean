/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1309 : Family 9 := level9.get ⟨74,by decide⟩
def sourceMap1309 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1309 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1309_checked : acceptsGraphIso
    (source (graph core1309) (root 9) 0 0) SmallGeFourSpectrum097.graph sourceMap1309=true := by decide +kernel
theorem fusedMap1309_checked : acceptsGraphIso
    (fused (graph core1309) (root 9) 0 0) SmallGeFourSpectrum104.graph fusedMap1309=true := by decide +kernel
theorem certified1309 : Certified (graph core1309) (root 9) 0 0 :=
  of_native_maps core1309 SmallGeFourSpectrum097.graph SmallGeFourSpectrum104.graph
    sourceMap1309 fusedMap1309 sourceMap1309_checked fusedMap1309_checked
    DegreeOneSmallComparisons.comparison1309
#print axioms sourceMap1309_checked
#print axioms fusedMap1309_checked
#print axioms certified1309
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
