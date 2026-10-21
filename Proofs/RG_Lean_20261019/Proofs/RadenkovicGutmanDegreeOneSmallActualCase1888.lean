/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1888 : Family 10 := level10.get ⟨156,by decide⟩
def sourceMap1888 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1888 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1888_checked : acceptsGraphIso
    (source (graph core1888) (root 10) 0 0) DegreeOneSmallSpectrum1226.graph sourceMap1888=true := by decide +kernel
theorem fusedMap1888_checked : acceptsGraphIso
    (fused (graph core1888) (root 10) 0 0) DegreeOneSmallSpectrum973.graph fusedMap1888=true := by decide +kernel
theorem certified1888 : Certified (graph core1888) (root 10) 0 0 :=
  of_native_maps core1888 DegreeOneSmallSpectrum1226.graph DegreeOneSmallSpectrum973.graph
    sourceMap1888 fusedMap1888 sourceMap1888_checked fusedMap1888_checked
    DegreeOneSmallComparisons.comparison1888
#print axioms sourceMap1888_checked
#print axioms fusedMap1888_checked
#print axioms certified1888
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
