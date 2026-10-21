/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1062 : Family 8 := level8.get ⟨132,by decide⟩
def sourceMap1062 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1062 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1062_checked : acceptsGraphIso
    (source (graph core1062) (root 8) 1 1) DegreeOneSmallSpectrum1894.graph sourceMap1062=true := by decide +kernel
theorem fusedMap1062_checked : acceptsGraphIso
    (fused (graph core1062) (root 8) 1 1) DegreeOneSmallSpectrum1296.graph fusedMap1062=true := by decide +kernel
theorem certified1062 : Certified (graph core1062) (root 8) 1 1 :=
  of_native_maps core1062 DegreeOneSmallSpectrum1894.graph DegreeOneSmallSpectrum1296.graph
    sourceMap1062 fusedMap1062 sourceMap1062_checked fusedMap1062_checked
    DegreeOneSmallComparisons.comparison1062
#print axioms sourceMap1062_checked
#print axioms fusedMap1062_checked
#print axioms certified1062
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
