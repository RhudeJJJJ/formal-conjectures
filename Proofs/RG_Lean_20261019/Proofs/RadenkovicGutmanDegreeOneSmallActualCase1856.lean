/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1856 : Family 10 := level10.get ⟨111,by decide⟩
def sourceMap1856 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1856 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1856_checked : acceptsGraphIso
    (source (graph core1856) (root 10) 0 0) DegreeOneSmallSpectrum1222.graph sourceMap1856=true := by decide +kernel
theorem fusedMap1856_checked : acceptsGraphIso
    (fused (graph core1856) (root 10) 0 0) DegreeOneSmallSpectrum942.graph fusedMap1856=true := by decide +kernel
theorem certified1856 : Certified (graph core1856) (root 10) 0 0 :=
  of_native_maps core1856 DegreeOneSmallSpectrum1222.graph DegreeOneSmallSpectrum942.graph
    sourceMap1856 fusedMap1856 sourceMap1856_checked fusedMap1856_checked
    DegreeOneSmallComparisons.comparison1856
#print axioms sourceMap1856_checked
#print axioms fusedMap1856_checked
#print axioms certified1856
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
