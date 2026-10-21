/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1043 : Family 8 := level8.get ⟨120,by decide⟩
def sourceMap1043 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (sourceLabel 8 0 0 v)
def fusedMap1043 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap1043_checked : acceptsGraphIso
    (source (graph core1043) (root 8) 0 0) DegreeOneSmallSpectrum313.graph sourceMap1043=true := by decide +kernel
theorem fusedMap1043_checked : acceptsGraphIso
    (fused (graph core1043) (root 8) 0 0) DegreeOneSmallSpectrum312.graph fusedMap1043=true := by decide +kernel
theorem certified1043 : Certified (graph core1043) (root 8) 0 0 :=
  of_native_maps core1043 DegreeOneSmallSpectrum313.graph DegreeOneSmallSpectrum312.graph
    sourceMap1043 fusedMap1043 sourceMap1043_checked fusedMap1043_checked
    DegreeOneSmallComparisons.comparison1043
#print axioms sourceMap1043_checked
#print axioms fusedMap1043_checked
#print axioms certified1043
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
