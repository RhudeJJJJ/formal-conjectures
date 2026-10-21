/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1233 : Family 9 := level9.get ⟨21,by decide⟩
def sourceMap1233 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,6,4,5] (sourceLabel 9 0 0 v)
def fusedMap1233 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1233_checked : acceptsGraphIso
    (source (graph core1233) (root 9) 0 0) DegreeOneSmallSpectrum453.graph sourceMap1233=true := by decide +kernel
theorem fusedMap1233_checked : acceptsGraphIso
    (fused (graph core1233) (root 9) 0 0) DegreeOneSmallSpectrum384.graph fusedMap1233=true := by decide +kernel
theorem certified1233 : Certified (graph core1233) (root 9) 0 0 :=
  of_native_maps core1233 DegreeOneSmallSpectrum453.graph DegreeOneSmallSpectrum384.graph
    sourceMap1233 fusedMap1233 sourceMap1233_checked fusedMap1233_checked
    DegreeOneSmallComparisons.comparison1233
#print axioms sourceMap1233_checked
#print axioms fusedMap1233_checked
#print axioms certified1233
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
