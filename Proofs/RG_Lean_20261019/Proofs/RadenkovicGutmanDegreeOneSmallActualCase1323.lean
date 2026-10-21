/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1323 : Family 9 := level9.get ⟨82,by decide⟩
def sourceMap1323 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1323 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1323_checked : acceptsGraphIso
    (source (graph core1323) (root 9) 0 0) DegreeOneSmallSpectrum452.graph sourceMap1323=true := by decide +kernel
theorem fusedMap1323_checked : acceptsGraphIso
    (fused (graph core1323) (root 9) 0 0) DegreeOneSmallSpectrum549.graph fusedMap1323=true := by decide +kernel
theorem certified1323 : Certified (graph core1323) (root 9) 0 0 :=
  of_native_maps core1323 DegreeOneSmallSpectrum452.graph DegreeOneSmallSpectrum549.graph
    sourceMap1323 fusedMap1323 sourceMap1323_checked fusedMap1323_checked
    DegreeOneSmallComparisons.comparison1323
#print axioms sourceMap1323_checked
#print axioms fusedMap1323_checked
#print axioms certified1323
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
