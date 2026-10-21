/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1871 : Family 10 := level10.get ⟨132,by decide⟩
def sourceMap1871 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1871 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1871_checked : acceptsGraphIso
    (source (graph core1871) (root 10) 0 0) DegreeOneSmallSpectrum1287.graph sourceMap1871=true := by decide +kernel
theorem fusedMap1871_checked : acceptsGraphIso
    (fused (graph core1871) (root 10) 0 0) DegreeOneSmallSpectrum958.graph fusedMap1871=true := by decide +kernel
theorem certified1871 : Certified (graph core1871) (root 10) 0 0 :=
  of_native_maps core1871 DegreeOneSmallSpectrum1287.graph DegreeOneSmallSpectrum958.graph
    sourceMap1871 fusedMap1871 sourceMap1871_checked fusedMap1871_checked
    DegreeOneSmallComparisons.comparison1871
#print axioms sourceMap1871_checked
#print axioms fusedMap1871_checked
#print axioms certified1871
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
